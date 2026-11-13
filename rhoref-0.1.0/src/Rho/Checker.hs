-- | The step-refinement checker (spec, Section 8.3).
--
-- The checker follows a machine run through its decision, insert, residue and
-- egress streams, maintains the abstract state as reference terms, and checks
-- every step against the reference semantics of "Rho.Core".
module Rho.Checker
  ( Abs(..), absProc, RunResult(..), runChecked, compileSource, symName
  ) where

import Control.Monad (unless, when)
import qualified Data.IntMap.Strict as IM
import Data.List (elemIndex, sort)
import qualified Data.Set as S
import Data.Word (Word32)

import Rho.Core
import Rho.Machine
import Rho.Syntax (parseProgram)

-- | The abstract state: one reference term per occupied slot, and the residue.
data Abs = Abs { aS :: IM.IntMap Proc, aR :: IM.IntMap Proc, aRes :: (Int, Int) } deriving (Eq, Show)

absProc :: Abs -> Proc
absProc a = mkPar (IM.elems (aS a) ++ IM.elems (aR a) ++ replicate t (PBool True) ++ replicate f (PBool False))
  where (t, f) = aRes a

data Dec = DInsS Int Proc | DInsR Int Proc | DRes Bool | DEg Proc

decProc :: Dec -> Proc
decProc d = case d of
  DInsS _ p -> p
  DInsR _ p -> p
  DRes b -> PBool b
  DEg p -> p

showF :: Fault -> String
showF = show

decode :: Mach -> Event -> Either String Dec
decode m ev = case ev of
  EvInsS i c p -> DInsS i <$> rd (PSend <$> readN c <*> readP p)
  EvInsR i e -> DInsR i <$> rd (entryProc e)
  EvResidue b -> Right (DRes b)
  EvEgress c p -> DEg <$> rd (PSend <$> readN c <*> readP p)
  _ -> Left ("unexpected event inside a step: " ++ show ev)
  where rd act = either (Left . ("decode: " ++) . showF) Right (fst (runMM act m))

applyDecs :: S.Set Name -> Abs -> [Dec] -> Either String Abs
applyDecs eg = go
  where
    go a [] = Right a
    go a (d : ds) = case d of
      DInsS i p@(PSend c _) -> do
        when (c `S.member` eg) (Left "a send on an egress channel was stored")
        when (IM.member i (aS a)) (Left ("send slot " ++ show i ++ " overwritten"))
        go a { aS = IM.insert i p (aS a) } ds
      DInsR i p -> do
        when (IM.member i (aR a)) (Left ("receive slot " ++ show i ++ " overwritten"))
        go a { aR = IM.insert i p (aR a) } ds
      DRes b -> let (t, f) = aRes a in go a { aRes = if b then (t + 1, f) else (t, f + 1) } ds
      DEg (PSend c _) -> do
        unless (c `S.member` eg) (Left "egress on a channel that is not a port")
        go a ds
      _ -> Left "malformed insert"

-- | Check the events of one step against the reference; return the new
-- abstract state.
checkStep :: S.Set Name -> Mach -> Abs -> [Event] -> Either String Abs
checkStep eg m a evs = case evs of
  [EvQuiescent] -> case redexes (absProc a) of
    Right [] -> Right a
    Right _ -> Left "quiescence reported, but the reference state has a redex"
    Left f -> Left ("reference fault at quiescence: " ++ showF f)
  (EvDecision _ s r row : rest) -> do
    snd' <- maybe (Left ("decision names empty send slot " ++ show s)) Right (IM.lookup s (aS a))
    rcv <- maybe (Left ("decision names empty receive slot " ++ show r)) Right (IM.lookup r (aR a))
    case (snd', rcv) of
      (PSend c q, PRecv pers c' pat body) -> do
        unless (c == c') (Left "decision joins different channels")
        sols <- either (Left . ("reference match fault: " ++) . showF) Right (matchSpec pat (mkQuote q))
        vals <- maybe (Left ("row " ++ show row ++ " is not in the reference match set")) Right (lookup row sols)
        red <- either (Left . ("reference instantiation fault: " ++) . showF) Right (inst (reverse vals) 0 body)
        ds <- mapM (decode m) rest
        let dut = sort (map decProc ds)
            ref = sort (comps red)
        unless (dut == ref) $ Left $ unlines
          [ "reduct mismatch at send slot " ++ show s ++ ", receive slot " ++ show r ++ ", row " ++ show row
          , "  machine:   " ++ ppProc [] (mkPar dut)
          , "  reference: " ++ ppProc [] (mkPar ref) ]
        let a1 = a { aS = IM.delete s (aS a), aR = if pers then aR a else IM.delete r (aR a) }
        applyDecs eg a1 ds
      _ -> Left "abstract slots hold the wrong kind of term"
  _ -> Left ("unexpected event shape: " ++ show (take 3 evs))

data RunResult = RunResult
  { rrDecisions :: [(Int, Int, Int)]   -- ^ the decision log: send slot, receive slot, row
  , rrEgress :: [Proc]                 -- ^ sends emitted on ports, in order
  , rrStates :: [Proc]                 -- ^ the abstraction at every boundary
  , rrQuiescent :: Bool
  , rrFault :: Maybe Fault
  , rrFinal :: Mach
  }

-- | Load a program and run it for at most the given number of steps, checking
-- the load, every step, the abstraction function and the audit invariants.
-- A machine fault ends the run and is reported in the result; a discrepancy
-- with the reference is a 'Left'.
runChecked :: Params -> Word32 -> [Name] -> Proc -> Int -> Either String RunResult
runChecked ps seed egNames prog maxSteps = do
  let eg = S.fromList egNames
      (evs0, m0) = takeEvents (load ps seed egNames prog)
  case fault m0 of
    Just f -> Right (RunResult [] [] [] False (Just f) m0)
    Nothing -> do
      ds0 <- mapM (decode m0) evs0
      a0 <- applyDecs eg (Abs IM.empty IM.empty (0, 0)) ds0
      let eg0 = [p | DEg p <- ds0]
      unless (mkPar (absProc a0 : eg0) == prog) (Left "the loaded image does not stand for the program")
      boundary m0 a0
      loop eg (0 :: Int) m0 a0 [] (reverse eg0) [absProc a0]
  where
    boundary m a = do
      case audit m of
        [] -> Right ()
        vs -> Left (unlines ("audit failed:" : vs))
      case alpha m of
        Right p | p == absProc a -> Right ()
        Right _ -> Left "the abstraction function disagrees with the event streams"
        Left f -> Left ("abstraction fault: " ++ showF f)
    finish m decs egs sts q = Right (RunResult (reverse decs) (reverse egs) (reverse sts) q (fault m) m)
    loop eg k m a decs egs sts
      | k >= maxSteps = finish m decs egs sts False
      | otherwise = do
          let (progress, m1) = stepM m
              (evs, m2) = takeEvents m1
          case fault m2 of
            Just _ -> finish m2 decs egs sts False
            Nothing -> do
              a' <- checkStep eg m2 a evs
              boundary m2 a'
              if not progress
                then finish m2 decs egs sts True
                else do
                  let decs' = [(s, r, row) | EvDecision _ s r row <- evs] ++ decs
                  unless (length [() | EvDecision {} <- evs] == 1) (Left "a step wrote other than one decision record")
                  new <- mapM (decode m2) [e | e@(EvEgress _ _) <- evs]
                  loop eg (k + 1) m2 a' decs' (reverse (map decProc new) ++ egs) (absProc a' : sts)

-- | Parse, scope and normalise a source program.  Returns the normal form and
-- the symbol table.
compileSource :: String -> Either String (Proc, [String])
compileSource src = do
  sp <- parseProgram src
  (raw, syms) <- scope sp
  p <- either (Left . ("rejected: " ++) . showF) Right (normalise raw)
  Right (p, syms)

-- | The closed name a symbol stands for.
symName :: [String] -> String -> Maybe Name
symName syms w = do
  k <- elemIndex w syms
  either (const Nothing) Just (normName (numeral k))
