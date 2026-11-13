{-# LANGUAGE LambdaCase #-}
-- | A word-level software model of the target machine (spec, Section 5).
--
-- The model has the machine's state (hash-consed heap with reference counts,
-- send and receive tables, residue, entropy) and takes the machine's steps
-- (pick, match, commit, explode).  It abstracts from clock cycles and from the
-- packing of nodes into memory words.
module Rho.Machine
  ( Params(..), defaultParams
  , PW(..), NW(..), Node(..), REntry(..), Event(..), Mach(..)
  , MM, runMM
  , load, step, stepForced, stepM, replayM, ingress
  , alpha, readP, readN, internP, internN, internRaw, instPW, entryProc
  , runPatW, lfsrStep, pick, nthSet, audit, takeEvents
  ) where

import Control.Monad (foldM, forM_, unless, when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict (State, get, gets, modify', put, runState)
import Data.Bits
import qualified Data.IntMap.Strict as IM
import Data.List (sort)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Word (Word32, Word64)

import Rho.Core

data Params = Params
  { nS :: Int        -- ^ send-table entries
  , nR :: Int        -- ^ receive-table entries
  , heapCap :: Int   -- ^ heap nodes
  , envMax :: Int    -- ^ E: maximum environment length
  , stackMax :: Int  -- ^ D: work-stack depth
  } deriving (Eq, Show)

defaultParams :: Params
defaultParams = Params { nS = 64, nR = 64, heapCap = 4096, envMax = 16, stackMax = 32 }

-- | Process words and name words (spec, Section 5.2).
data PW = WZero | WBool Bool | WPtr Int deriving (Eq, Ord, Show)
data NW = QZ | QB Bool | QP Int | QV Int deriving (Eq, Ord, Show)

data Node
  = NPar PW PW                 -- ^ head, tail: a sorted cons list
  | NSend NW PW
  | NRecv NW Int PW Int Bool   -- ^ channel, pattern address, body, nvars, persistent
  | NDrop NW                   -- ^ always of a variable
  | NBfn [Int] Word64
  deriving (Eq, Ord, Show)

-- | A receive in the soup: a closure of shared code and an environment.
data REntry = REntry
  { reChan :: NW, rePat :: Int, reBody :: PW, reN :: Int, reEnv :: [NW], rePers :: Bool }
  deriving (Eq, Show)

-- | The decision, insert, residue and egress streams (spec, Section 5.10).
data Event
  = EvDecision Int Int Int Int   -- ^ step, send slot, receive slot, row
  | EvInsS Int NW PW
  | EvInsR Int REntry
  | EvResidue Bool
  | EvEgress NW PW
  | EvQuiescent
  | EvFault Fault
  deriving (Eq, Show)

data Mach = Mach
  { params :: Params
  , hNodes :: IM.IntMap Node
  , hIndex :: M.Map Node Int      -- ^ the hash-cons table
  , hFv :: IM.IntMap Int          -- ^ header: free-variable depth (0 = closed)
  , hRc :: IM.IntMap Int
  , hFree :: [Int]
  , hNext :: Int
  , pats :: IM.IntMap Pat
  , patIx :: M.Map Pat Int
  , sTab :: IM.IntMap (NW, PW)
  , rTab :: IM.IntMap REntry
  , residue :: (Int, Int)         -- ^ counts of top-level true, false
  , egress :: S.Set NW
  , lfsr :: Word32
  , stepNo :: Int
  , quiescent :: Bool
  , fault :: Maybe Fault
  , events :: [Event]             -- ^ newest first
  } deriving (Show)

type MM = ExceptT Fault (State Mach)

runMM :: MM a -> Mach -> (Either Fault a, Mach)
runMM = runState . runExceptT

emit :: Event -> MM ()
emit e = modify' (\m -> m { events = e : events m })

takeEvents :: Mach -> ([Event], Mach)
takeEvents m = (reverse (events m), m { events = [] })

internal :: String -> MM a
internal = throwError . FaultInternal

------------------------------------------------------------------------------
-- Heap

node :: Int -> MM Node
node a = gets (IM.lookup a . hNodes) >>= maybe (internal ("dangling address " ++ show a)) pure

ptrsPW :: PW -> [Int]
ptrsPW (WPtr a) = [a]
ptrsPW _ = []

ptrsNW :: NW -> [Int]
ptrsNW (QP a) = [a]
ptrsNW _ = []

children :: Node -> [Int]
children = \case
  NPar h t -> ptrsPW h ++ ptrsPW t
  NSend c p -> ptrsNW c ++ ptrsPW p
  NRecv c _ b _ _ -> ptrsNW c ++ ptrsPW b
  NDrop n -> ptrsNW n
  NBfn _ _ -> []

fvPW :: PW -> MM Int
fvPW (WPtr a) = gets (IM.findWithDefault 0 a . hFv)
fvPW _ = pure 0

fvNW :: NW -> MM Int
fvNW (QP a) = gets (IM.findWithDefault 0 a . hFv)
fvNW (QV i) = pure (i + 1)
fvNW _ = pure 0

nodeFv :: Node -> MM Int
nodeFv = \case
  NPar h t -> max <$> fvPW h <*> fvPW t
  NSend c p -> max <$> fvNW c <*> fvPW p
  NRecv c _ b n _ -> (\x y -> max x (max 0 (y - n))) <$> fvNW c <*> fvPW b
  NDrop n -> fvNW n
  NBfn s _ -> pure (if null s then 0 else maximum s + 1)

incRc, decRc :: Int -> MM ()
incRc a = modify' (\m -> m { hRc = IM.insertWith (+) a 1 (hRc m) })
decRc a = modify' (\m -> m { hRc = IM.adjust (subtract 1) a (hRc m) })

-- | Return the address of the unique stored node equal to the argument.
intern :: Node -> MM Int
intern nd = do
  m <- get
  case M.lookup nd (hIndex m) of
    Just a -> pure a
    Nothing -> do
      when (IM.size (hNodes m) >= heapCap (params m)) (throwError FaultHeap)
      fv <- nodeFv nd
      let (a, free', next') = case hFree m of
            (x : xs) -> (x, xs, hNext m)
            [] -> (hNext m, [], hNext m + 1)
      put m { hNodes = IM.insert a nd (hNodes m), hIndex = M.insert nd a (hIndex m)
            , hFv = IM.insert a fv (hFv m), hRc = IM.insert a 0 (hRc m)
            , hFree = free', hNext = next' }
      mapM_ incRc (children nd)
      pure a

-- | Deferred free: reclaim every node whose count is zero, cascading.
sweep :: MM ()
sweep = do
  m <- get
  case [a | (a, 0) <- IM.toList (hRc m)] of
    [] -> pure ()
    zs -> do
      forM_ zs $ \a -> do
        nd <- node a
        modify' (\s -> s { hNodes = IM.delete a (hNodes s), hIndex = M.delete nd (hIndex s)
                         , hFv = IM.delete a (hFv s), hRc = IM.delete a (hRc s)
                         , hFree = a : hFree s })
        mapM_ decRc (children nd)
      sweep

internPat :: Pat -> MM Int
internPat p = do
  m <- get
  case M.lookup p (patIx m) of
    Just a -> pure a
    Nothing -> do
      let a = IM.size (pats m)
      put m { pats = IM.insert a p (pats m), patIx = M.insert p a (patIx m) }
      pure a

getPat :: Int -> MM Pat
getPat a = gets (IM.lookup a . pats) >>= maybe (internal "dangling pattern address") pure

------------------------------------------------------------------------------
-- Normalising constructors

compsW :: PW -> MM [PW]
compsW WZero = pure []
compsW w@(WPtr a) = node a >>= \case
  NPar h t -> (h :) <$> compsW t
  _ -> pure [w]
compsW w = pure [w]

mkParW :: PW -> PW -> MM PW
mkParW a b = do
  xs <- compsW a
  ys <- compsW b
  build (sort (xs ++ ys))
  where
    build [] = pure WZero
    build [p] = pure p
    build (p : ps) = build ps >>= \t -> WPtr <$> intern (NPar p t)

mkDropW :: NW -> MM PW
mkDropW = \case
  QZ -> pure WZero
  QB b -> pure (WBool b)
  QP a -> pure (WPtr a)
  QV i -> WPtr <$> intern (NDrop (QV i))

mkQuoteW :: PW -> MM NW
mkQuoteW = \case
  WZero -> pure QZ
  WBool b -> pure (QB b)
  WPtr a -> node a >>= \case
    NDrop (QV i) -> pure (QV i)
    _ -> pure (QP a)

mkBfnW :: BF -> MM PW
mkBfnW bf = case minimise bf of
  BF [] t -> pure (WBool (t == 1))
  BF [i] 2 -> mkDropW (QV i)
  BF s t
    | length s > kMax -> throwError (FaultWide (length s))
    | otherwise -> WPtr <$> intern (NBfn s (fromInteger t))

internP :: Proc -> MM PW
internP = \case
  PPar ps -> mapM internP ps >>= foldM mkParW WZero
  PBool b -> pure (WBool b)
  PSend n q -> do c <- internN n; p <- internP q; WPtr <$> intern (NSend c p)
  PRecv pers n pat b -> do
    c <- internN n
    pa <- internPat pat
    w <- internP b
    WPtr <$> intern (NRecv c pa w (pVars pat) pers)
  PDrop i -> mkDropW (QV i)
  PBfn s t -> mkBfnW (BF s (toInteger t))

internN :: Name -> MM NW
internN (NQ p) = internP p >>= mkQuoteW
internN (NVar i) = pure (QV i)

-- | Intern an un-normalised term using the machine's normalising
-- constructors alone, with no help from the reference normaliser.  This is
-- the interner algorithm that the compiler and the hardware must share.
internRaw :: Raw -> MM PW
internRaw = \case
  RNil -> pure WZero
  RBool b -> pure (WBool b)
  RNot a -> internRaw a >>= toBFW >>= mkBfnW . bfNot
  RBin op a b -> do
    x <- internRaw a >>= toBFW
    y <- internRaw b >>= toBFW
    mkBfnW (bfBin op x y)
  RRecv pers n pat b -> do
    c <- internRawN n
    pa <- internPat pat
    w <- internRaw b
    WPtr <$> intern (NRecv c pa w (pVars pat) pers)
  RSend n q -> do c <- internRawN n; p <- internRaw q; WPtr <$> intern (NSend c p)
  RPar a b -> do x <- internRaw a; y <- internRaw b; mkParW x y
  RDrop n -> internRawN n >>= mkDropW
  where
    internRawN (RQ r) = internRaw r >>= mkQuoteW
    internRawN (RV i) = pure (QV i)
    toBFW = \case
      WBool b -> pure (bfConst b)
      WPtr a -> node a >>= \case
        NDrop (QV i) -> pure (bfVar i)
        NBfn s t -> pure (BF s (toInteger t))
        _ -> throwError (FaultSort "non-Boolean operand")
      WZero -> throwError (FaultSort "non-Boolean operand")

readP :: PW -> MM Proc
readP = \case
  WZero -> pure nil
  WBool b -> pure (PBool b)
  WPtr a -> node a >>= \case
    NPar h t -> (\x y -> mkPar [x, y]) <$> readP h <*> readP t
    NSend c p -> PSend <$> readN c <*> readP p
    NRecv c pa b _ pers -> do n <- readN c; pat <- getPat pa; PRecv pers n pat <$> readP b
    NDrop n -> mkDrop <$> readN n
    NBfn s t -> pure (PBfn s t)

readN :: NW -> MM Name
readN = \case
  QZ -> pure (NQ nil)
  QB b -> pure (NQ (PBool b))
  QP a -> mkQuote <$> readP (WPtr a)
  QV i -> pure (NVar i)

------------------------------------------------------------------------------
-- Instantiation (spec, Section 5.8)

envAt :: [NW] -> Int -> MM NW
envAt env i
  | i >= 0 && i < length env = pure (env !! i)
  | otherwise = internal "variable beyond the environment"

instPW :: [NW] -> Int -> PW -> MM PW
instPW env k pw = do
  fv <- fvPW pw
  if fv <= k then pure pw else case pw of
    WPtr a -> node a >>= \case
      NPar h t -> do x <- instPW env k h; y <- instPW env k t; mkParW x y
      NSend c p -> do c' <- instNW env k c; p' <- instPW env k p; WPtr <$> intern (NSend c' p')
      NRecv c pa b n pers -> do
        c' <- instNW env k c
        b' <- instPW env (k + n) b
        WPtr <$> intern (NRecv c' pa b' n pers)
      NDrop (QV i) -> envAt env (i - k) >>= mkDropW
      NDrop _ -> internal "drop of a non-variable in the heap"
      NBfn s t -> do
        let stepv bf (p, v)
              | v < k = pure bf
              | otherwise = envAt env (v - k) >>= \case
                  QB b -> pure (restrict p b bf)
                  _ -> throwError (FaultSort "Boolean operand met a non-Boolean name")
        foldM stepv (BF s (toInteger t)) (reverse (zip [0 ..] s)) >>= mkBfnW
    _ -> pure pw

instNW :: [NW] -> Int -> NW -> MM NW
instNW env k = \case
  QV i | i < k -> pure (QV i)
       | otherwise -> envAt env (i - k)
  QP a -> do
    fv <- fvNW (QP a)
    if fv <= k then pure (QP a) else instPW env k (WPtr a) >>= mkQuoteW
  w -> pure w

------------------------------------------------------------------------------
-- Tables

freeSlot :: Int -> IM.IntMap a -> Maybe Int
freeSlot n t = case [i | i <- [0 .. n - 1], not (IM.member i t)] of
  (i : _) -> Just i
  [] -> Nothing

insertS :: NW -> PW -> MM ()
insertS c p = do
  m <- get
  case freeSlot (nS (params m)) (sTab m) of
    Nothing -> throwError FaultStore
    Just i -> do
      put m { sTab = IM.insert i (c, p) (sTab m) }
      mapM_ incRc (ptrsNW c ++ ptrsPW p)
      emit (EvInsS i c p)

entryPtrs :: REntry -> [Int]
entryPtrs e = ptrsNW (reChan e) ++ ptrsPW (reBody e) ++ concatMap ptrsNW (reEnv e)

insertR :: REntry -> MM ()
insertR e = do
  m <- get
  when (length (reEnv e) > envMax (params m)) (throwError FaultHeap)
  case freeSlot (nR (params m)) (rTab m) of
    Nothing -> throwError FaultStore
    Just i -> do
      put m { rTab = IM.insert i e (rTab m) }
      mapM_ incRc (entryPtrs e)
      emit (EvInsR i e)

removeS :: Int -> MM ()
removeS i = do
  (c, p) <- gets (IM.lookup i . sTab) >>= maybe (internal "empty send slot") pure
  modify' (\m -> m { sTab = IM.delete i (sTab m) })
  mapM_ decRc (ptrsNW c ++ ptrsPW p)

removeR :: Int -> MM ()
removeR i = do
  e <- gets (IM.lookup i . rTab) >>= maybe (internal "empty receive slot") pure
  modify' (\m -> m { rTab = IM.delete i (rTab m) })
  mapM_ decRc (entryPtrs e)

------------------------------------------------------------------------------
-- Arbiter (spec, Section 5.6)

-- | One shift of a maximal-length 32-bit Galois LFSR (taps 32, 22, 2, 1).
lfsrStep :: Word32 -> Word32
lfsrStep x = let y = x `shiftR` 1 in if testBit x 0 then y `xor` 0x80200003 else y

-- | Map an entropy sample to a choice in @[0, n)@.
pick :: Int -> Word32 -> Int
pick n w = fromIntegral ((fromIntegral w * fromIntegral n :: Word64) `shiftR` 32)

-- | The arbiter.  The LFSR advances 32 positions per choice.
choose :: Int -> MM Int
choose n
  | n <= 0 = internal "choose of an empty set"
  | otherwise = do
      w <- gets ((!! 32) . iterate lfsrStep . lfsr)
      modify' (\m -> m { lfsr = w })
      pure (pick n w)

-- | Index of the u-th set bit.
nthSet :: Word64 -> Int -> Int
nthSet mask u = [r | r <- [0 .. 63], testBit mask r] !! u

------------------------------------------------------------------------------
-- Matcher (spec, Section 5.5)

runPatW :: Pat -> NW -> MM (Maybe ([NW], Word64))
runPatW pat n0 = go (pOps pat) [n0] [] (validMask (pNB pat))
  where
    go [] [] bs m = pure (Just (reverse bs, m))
    go [] _ _ _ = internal "pattern program left the cursor stack non-empty"
    go _ [] _ _ = internal "pattern program ran out of cursor stack"
    go (op : ops) (n : st) bs m = case op of
      NBind -> go ops st (n : bs) m
      NEq i -> if reverse bs !! i == n then go ops st bs m else pure Nothing
      QZeroOp -> if n == QZ then go ops st bs m else pure Nothing
      QSendOp -> case n of
        QP a -> node a >>= \case
          NSend c q -> mkQuoteW q >>= \qn -> go ops (c : qn : st) bs m
          _ -> pure Nothing
        _ -> pure Nothing
      BLeaf t -> case n of
        QB b -> go ops st bs (m .&. (if b then t else complement t))
        _ -> throwError (FaultSort "Boolean leaf met a non-Boolean name")

------------------------------------------------------------------------------
-- Explode and the step (spec, Section 5.7)

res :: Bool -> MM ()
res b = do
  modify' (\m -> let (t, f) = residue m in m { residue = if b then (t + 1, f) else (t, f + 1) })
  emit (EvResidue b)

explode :: [(PW, [NW])] -> MM ()
explode [] = pure ()
explode st@((pw, env) : rest) = do
  d <- gets (stackMax . params)
  when (length st > d) (throwError FaultStack)
  case pw of
    WZero -> explode rest
    WBool b -> res b >> explode rest
    WPtr a -> node a >>= \case
      NPar h t -> explode ((h, env) : (t, env) : rest)
      NSend c q -> do
        c' <- instNW env 0 c
        q' <- instPW env 0 q
        eg <- gets egress
        if c' `S.member` eg then emit (EvEgress c' q') else insertS c' q'
        explode rest
      NRecv c pa b n pers -> do
        c' <- instNW env 0 c
        insertR (REntry c' pa b n env pers)
        explode rest
      NDrop (QV i) -> envAt env i >>= \case
        QZ -> explode rest
        QB b -> res b >> explode rest
        QP a' -> explode ((WPtr a', []) : rest)
        QV _ -> internal "open name in an environment"
      NDrop _ -> internal "drop of a non-variable in the heap"
      NBfn s t -> do
        bits <- mapM (\v -> envAt env v >>= \case
                        QB b -> pure b
                        _ -> throwError (FaultSort "Boolean operand met a non-Boolean name")) s
        let row = foldl (.|.) 0 [bit j | (j, True) <- zip [0 ..] bits] :: Int
        res (testBit t row)
        explode rest

commit :: Int -> Int -> REntry -> Pat -> [NW] -> Word64 -> Maybe Int -> MM ()
commit s r e pat structs mask forced = do
  row <- case forced of
    Just x -> pure x
    Nothing -> nthSet mask <$> choose (popCount mask)
  unless (testBit mask row) (internal "chosen row is not a solution")
  n <- gets stepNo
  emit (EvDecision n s r row)
  removeS s
  unless (rePers e) (removeR r)
  let bools = [QB (testBit row j) | j <- [0 .. pNB pat - 1]]
  explode [(reBody e, reverse (structs ++ bools) ++ reEnv e)]
  modify' (\m -> m { stepNo = stepNo m + 1 })

-- | One step from a boundary.  Returns False when the soup is quiescent.
step :: MM Bool
step = do
  sweep
  modify' (\m -> m { quiescent = False })
  gets (IM.keys . sTab) >>= scan
  where
    scan [] = do
      modify' (\m -> m { quiescent = True })
      emit EvQuiescent
      pure False
    scan ss = do
      s <- (ss !!) <$> choose (length ss)
      (c, q) <- gets ((IM.! s) . sTab)
      rs <- gets (\m -> [r | (r, e) <- IM.toList (rTab m), reChan e == c])
      tryR s q (filter (/= s) ss) rs
    tryR _ _ ss' [] = scan ss'
    tryR s q ss' rs = do
      r <- (rs !!) <$> choose (length rs)
      e <- gets ((IM.! r) . rTab)
      pat <- getPat (rePat e)
      qn <- mkQuoteW q
      runPatW pat qn >>= \case
        Just (structs, mask) | mask /= 0 -> commit s r e pat structs mask Nothing >> pure True
        _ -> tryR s q ss' (filter (/= r) rs)

-- | Replay one step from a decision record.
stepForced :: (Int, Int, Int) -> MM ()
stepForced (s, r, row) = do
  sweep
  (c, q) <- gets (IM.lookup s . sTab) >>= maybe (internal "replay: empty send slot") pure
  e <- gets (IM.lookup r . rTab) >>= maybe (internal "replay: empty receive slot") pure
  unless (reChan e == c) (internal "replay: channels differ")
  pat <- getPat (rePat e)
  qn <- mkQuoteW q
  runPatW pat qn >>= \case
    Just (structs, mask) | testBit mask row -> commit s r e pat structs mask (Just row)
    _ -> internal "replay: not a redex"

-- | Run an action; a fault becomes sticky state and an event.
guarded :: a -> MM a -> Mach -> (a, Mach)
guarded dflt act m
  | Just _ <- fault m = (dflt, m)
  | otherwise = case runMM act m of
      (Right a, m') -> (a, m')
      (Left f, m') -> (dflt, m' { fault = Just f, events = EvFault f : events m' })

stepM :: Mach -> (Bool, Mach)
stepM = guarded False step

replayM :: (Int, Int, Int) -> Mach -> Mach
replayM d = snd . guarded () (stepForced d)

-- | Ingress: insert a send on a channel at a boundary (spec, Section 5.9).
ingress :: Name -> Proc -> Mach -> Mach
ingress n q = snd . guarded () (do c <- internN n; p <- internP q; insertS c p)

-- | Build the initial machine from a closed normal-form process.
load :: Params -> Word32 -> [Name] -> Proc -> Mach
load ps seed egressNames prog = snd (guarded () act m0)
  where
    m0 = Mach { params = ps, hNodes = IM.empty, hIndex = M.empty, hFv = IM.empty, hRc = IM.empty
              , hFree = [], hNext = 0, pats = IM.empty, patIx = M.empty
              , sTab = IM.empty, rTab = IM.empty, residue = (0, 0), egress = S.empty
              , lfsr = if seed == 0 then 1 else seed, stepNo = 0, quiescent = False
              , fault = Nothing, events = [] }
    act = do
      ws <- mapM internN egressNames
      mapM_ (mapM_ incRc . ptrsNW) ws
      modify' (\m -> m { egress = S.fromList ws })
      w <- internP prog
      explode [(w, [])]

------------------------------------------------------------------------------
-- Abstraction and audit (spec, Section 8)

-- | The closed term a receive entry stands for.
entryProc :: REntry -> MM Proc
entryProc e = do
  c <- readN (reChan e)
  pat <- getPat (rePat e)
  b <- readP (reBody e)
  env <- mapM readN (reEnv e)
  b' <- either throwError pure (inst env (reN e) b)
  pure (PRecv (rePers e) c pat b')

-- | The abstraction function: the process a boundary state stands for.
alpha :: Mach -> Either Fault Proc
alpha m = fst (runMM act m)
  where
    act = do
      ss <- mapM (\(c, p) -> PSend <$> readN c <*> readP p) (IM.elems (sTab m))
      rs <- mapM entryProc (IM.elems (rTab m))
      let (t, f) = residue m
      pure (mkPar (ss ++ rs ++ replicate t (PBool True) ++ replicate f (PBool False)))

-- | Check the boundary invariants I1-I5; returns the violations.
audit :: Mach -> [String]
audit m = concat [i1, i2, i3, i4]
  where
    run act = fst (runMM act m)
    addrs = IM.keys (hNodes m)
    -- I1, I5: every stored node is canonical: re-interning its readback
    -- returns the same address and allocates nothing.
    i1 = concat
      [ case runMM (readP (WPtr a) >>= internP) m of
          (Right (WPtr a'), m') | a' == a && IM.size (hNodes m') == IM.size (hNodes m) -> []
          (Right (WPtr a'), m') | a' == a -> ["I1: re-interning node " ++ show a ++ " allocated ("
                                              ++ show (IM.size (hNodes m') - IM.size (hNodes m)) ++ ")"]
          other -> ["I1: node " ++ show a ++ " is not canonical: " ++ show (fst other)]
      | a <- addrs, canon a ]
    -- A bare drop node is only ever a component; its readback re-interns to itself too.
    canon _ = True
    -- I2: the hash-cons table is a bijection with the heap.
    i2 = [ "I2: hash-cons table and heap disagree"
         | M.size (hIndex m) /= IM.size (hNodes m)
           || any (\(a, nd) -> M.lookup nd (hIndex m) /= Just a) (IM.toList (hNodes m)) ]
    -- I3: reference counts equal the number of references.
    refs = concatMap children (IM.elems (hNodes m))
        ++ concat [ptrsNW c ++ ptrsPW p | (c, p) <- IM.elems (sTab m)]
        ++ concatMap entryPtrs (IM.elems (rTab m))
        ++ concatMap ptrsNW (S.toList (egress m))
    expected = IM.fromListWith (+) [(a, 1 :: Int) | a <- refs]
    i3 = [ "I3: node " ++ show a ++ " has count " ++ show c ++ ", expected " ++ show x
         | (a, c) <- IM.toList (hRc m), let x = IM.findWithDefault 0 a expected, x /= c ]
      ++ [ "I3: reference to a missing node " ++ show a | a <- IM.keys expected, not (IM.member a (hNodes m)) ]
    -- I4: store words and environment entries are closed.
    closedN w = run (fvNW w) == Right 0
    closedP w = run (fvPW w) == Right 0
    i4 = [ "I4: open word in send slot " ++ show i | (i, (c, p)) <- IM.toList (sTab m), not (closedN c && closedP p) ]
      ++ [ "I4: open word in receive slot " ++ show i
         | (i, e) <- IM.toList (rTab m), not (closedN (reChan e) && all closedN (reEnv e)) ]
