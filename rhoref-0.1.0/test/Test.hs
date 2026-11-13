{-# LANGUAGE LambdaCase #-}
-- | The verification suite: the layers of evidence of the spec (Section 8.2)
-- that can be discharged in software, and the directed programs (Section 8.5).
module Main (main) where

import Control.Monad (forM, replicateM, unless, when)
import Control.Monad.State.Strict (State, evalState, state)
import Data.Bits
import Data.Either (isLeft)
import Data.IORef
import Data.List (nub, sort)
import Data.Maybe (fromJust, mapMaybe)
import qualified Data.Set as S
import Data.Word (Word32, Word64)
import System.Exit (exitFailure)

import Rho.Checker
import Rho.Core
import Rho.Machine
import Rho.Syntax

------------------------------------------------------------------------------
-- A small deterministic generator (SplitMix64); no external packages.

type Gen = State Word64

next64 :: Gen Word64
next64 = state $ \s ->
  let s' = s + 0x9e3779b97f4a7c15
      z1 = (s' `xor` (s' `shiftR` 30)) * 0xbf58476d1ce4e5b9
      z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94d049bb133111eb
  in (z2 `xor` (z2 `shiftR` 31), s')

below :: Int -> Gen Int
below n = (\w -> fromIntegral (w `mod` fromIntegral n)) <$> next64

oneOf :: [a] -> Gen a
oneOf xs = (xs !!) <$> below (length xs)

chance :: Int -> Gen Bool
chance pct = (< pct) <$> below 100

------------------------------------------------------------------------------
-- Random raw terms and congruence-preserving rewrites (for V1 and V3)

patOf :: String -> Pat
patOf s = case parseProgram ("for(" ++ s ++ " <- @0){ 0 }") >>= scope of
  Right (RRecv _ _ p _, _) -> p
  other -> error ("bad test pattern " ++ s ++ ": " ++ show other)

testPats :: [Pat]
testPats = map patOf
  [ "a", "@0", "@true", "@false", "@(p && q)", "@(p xor q)", "@(~p)", "@(p || ~p)", "@(p && ~p)"
  , "@(a!(b))", "@(a!(p || q))", "@(@0!(v))", "@(a!(a))", "@(c!(p && q && r))", "@(@(p xor q)!(p))" ]

genB :: Int -> Int -> Gen Raw
genB d n
  | n <= 0 = if d > 0 then oneOf [0, 1, 2 :: Int] >>= \case
                              0 -> RBool <$> chance 50
                              _ -> RDrop . RV <$> below (min d 4)
                      else RBool <$> chance 50
  | otherwise = below 4 >>= \case
      0 -> RNot <$> genB d (n - 1)
      1 -> genB d 0
      _ -> RBin <$> oneOf [BAnd, BOr, BXor] <*> genB d (n `div` 2) <*> genB d (n `div` 2)

genN :: Int -> Int -> Gen RName
genN d n = below 4 >>= \case
  0 | d > 0 -> RV <$> below d
  1 -> RQ <$> genP d (n `div` 2)
  _ -> numeral <$> below 3

genP :: Int -> Int -> Gen Raw
genP d n
  | n <= 0 = below 4 >>= \case
      0 -> pure RNil
      1 -> RBool <$> chance 50
      2 | d > 0 -> RDrop . RV <$> below d
      _ -> pure RNil
  | otherwise = below 7 >>= \case
      0 -> RPar <$> genP d (n `div` 2) <*> genP d (n `div` 2)
      1 -> RPar <$> genP d (n `div` 2) <*> genP d (n `div` 2)
      2 -> RSend <$> genN d (n - 1) <*> genP d (n - 1)
      3 -> do
        pat <- oneOf testPats
        RRecv <$> chance 30 <*> genN d (n - 1) <*> pure pat <*> genP (d + pVars pat) (n - 1)
      4 -> genB d (n `div` 2)
      5 -> RDrop . RQ <$> genP d (n - 1)
      _ -> genP d 0

isBoolRoot :: Raw -> Bool
isBoolRoot = \case
  RBool _ -> True
  RNot _ -> True
  RBin {} -> True
  RDrop (RV _) -> True
  _ -> False

-- | Rewrite a term by laws of structural congruence, at random positions.
mutate :: Raw -> Gen Raw
mutate r0 = do
  r <- descend r0
  hit <- chance 35
  if hit then rewrite r else pure r
  where
    descend = \case
      RNot a -> RNot <$> mutate a
      RBin op a b -> RBin op <$> mutate a <*> mutate b
      RRecv pers n pat b -> RRecv pers <$> mutN n <*> pure pat <*> mutate b
      RSend n q -> RSend <$> mutN n <*> mutate q
      RPar a b -> RPar <$> mutate a <*> mutate b
      RDrop n -> RDrop <$> mutN n
      r -> pure r
    mutN = \case
      RQ r -> RQ <$> mutate r
      n -> chance 20 >>= \h -> pure (if h then RQ (RDrop n) else n)
    rewrite r = do
      let general = [RPar r RNil, RPar RNil r, RDrop (RQ r)]
          par = case r of
            RPar a b -> RPar b a : [RPar x (RPar y b) | RPar x y <- [a]]
            _ -> []
          bool = if not (isBoolRoot r) then [] else
            [ RNot (RNot r), RBin BAnd r (RBool True), RBin BOr r (RBool False), RBin BAnd r r
            , RBin BXor r (RBool False), RBin BOr r (RBin BAnd r (RBool False)) ]
            ++ case r of
                 RBin BAnd a b -> [RBin BAnd b a, RNot (RBin BOr (RNot a) (RNot b))]
                 RBin BOr a b -> [RBin BOr b a, RNot (RBin BAnd (RNot a) (RNot b))]
                 RBin BXor a b -> [RBin BXor b a, RBin BOr (RBin BAnd a (RNot b)) (RBin BAnd (RNot a) b)]
                 _ -> []
      oneOf (general ++ par ++ bool)

-- | A brute-force decision of structural congruence on raw terms.  It uses no
-- truth tables and no sorting: Boolean terms are compared by evaluation under
-- every assignment, compositions by searching for a matching of components.
equivRaw :: Raw -> Raw -> Bool
equivRaw a b = bagEq (components a) (components b)
  where
    components = \case
      RPar x y -> components x ++ components y
      RNil -> []
      RDrop (RQ p) -> components p
      x -> [x]
    boolish x = case components x of
      [y] -> isBoolRoot y
      _ -> False
    bvars x = case components x of
      [RNot p] -> bvars p
      [RBin _ p q] -> bvars p ++ bvars q
      [RDrop (RV i)] -> [i]
      _ -> []
    eval env x = case components x of
      [RBool v] -> v
      [RNot p] -> not (eval env p)
      [RBin BAnd p q] -> eval env p && eval env q
      [RBin BOr p q] -> eval env p || eval env q
      [RBin BXor p q] -> eval env p /= eval env q
      [RDrop (RV i)] -> fromJust (lookup i env)
      _ -> error "equivRaw: not Boolean"
    bagEq [] [] = True
    bagEq [] _ = False
    bagEq (x : xs) ys = case break (eqC x) ys of
      (_, []) -> False
      (pre, _ : post) -> bagEq xs (pre ++ post)
    eqC x y
      | boolish x && boolish y =
          let vs = nub (bvars x ++ bvars y)
          in and [ eval env x == eval env y
                 | r <- [0 .. bit (length vs) - 1 :: Int], let env = [(v, testBit r j) | (j, v) <- zip [0 ..] vs] ]
      | boolish x || boolish y = False
      | otherwise = case (x, y) of
          (RSend n q, RSend n' q') -> eqN n n' && equivRaw q q'
          (RRecv p n pat body, RRecv p' n' pat' body') ->
            p == p' && pat == pat' && eqN n n' && equivRaw body body'
          _ -> False
    viewN n = case n of
      RQ r | [RDrop n'] <- components' r -> viewN n'
      _ -> n
    components' r = case components r of
      [RDrop (RV i)] -> [RDrop (RV i)]
      other -> other
    eqN n n' = case (viewN n, viewN n') of
      (RV i, RV j) -> i == j
      (RQ p, RQ q) -> equivRaw p q
      -- a quoted Boolean term that is the identity on a variable names that variable
      (RV i, RQ q) -> equivRaw (RDrop (RV i)) q
      (RQ p, RV j) -> equivRaw p (RDrop (RV j))

------------------------------------------------------------------------------
-- Harness

type Check = IO (Either String String)

check :: IORef Int -> String -> Check -> IO ()
check fails name act = act >>= \case
  Right info -> putStrLn ("  ok    " ++ name ++ (if null info then "" else "  (" ++ info ++ ")"))
  Left err -> do
    putStrLn ("  FAIL  " ++ name)
    mapM_ (putStrLn . ("        " ++)) (take 12 (lines err))
    modifyIORef' fails (+ 1)

firstLeft :: [Either String a] -> Either String [a]
firstLeft = sequence

compileOrDie :: String -> (Proc, [String])
compileOrDie src = either (\e -> error ("test program does not compile: " ++ e ++ "\n" ++ src)) id (compileSource src)

data Outcome = Outcome { oEgress :: [String], oFinal :: String, oQuiet :: Bool, oFault :: Maybe Fault, oSteps :: Int }
  deriving (Eq, Show)

-- | Run a source program under the checker.  Egress outputs are sorted.
runSrc :: Params -> String -> [String] -> Word32 -> Int -> Either String (Outcome, RunResult)
runSrc ps src ports seed steps = do
  let (p, syms) = compileOrDie src
      eg = mapMaybe (symName syms) ports
  rr <- runChecked ps seed eg p steps
  let fin = if null (rrStates rr) then "" else ppProc syms (last (rrStates rr))
  Right (Outcome (sort (map (ppProc syms) (rrEgress rr))) fin (rrQuiescent rr) (rrFault rr) (length (rrDecisions rr)), rr)

seeds :: [Word32]
seeds = [1 .. 60]

-- | Every seed must give one of the expected (egress, final-state) outcomes,
-- quiescent and fault-free; and every expected outcome must occur.
expectOutcomes :: String -> [String] -> [([String], String)] -> Check
expectOutcomes src ports expected = pure $ do
  outs <- forM seeds $ \s -> do
    (o, _) <- runSrc defaultParams src ports s 200
    unless (oQuiet o && oFault o == Nothing) (Left ("seed " ++ show s ++ ": did not finish cleanly: " ++ show o))
    Right (oEgress o, oFinal o)
  let seen = nub outs
      want = [(sort e, f) | (e, f) <- expected]
  unless (all (`elem` want) seen) (Left ("unexpected outcome: " ++ show (filter (`notElem` want) seen)))
  unless (all (`elem` seen) want) (Left ("outcome never reached: " ++ show (filter (`notElem` seen) want)))
  Right (show (length seen) ++ " outcome(s) over " ++ show (length seeds) ++ " seeds")

------------------------------------------------------------------------------
-- V1, V3: canonicity

v1 :: Check
v1 = pure $ do
  let trial seed = flip evalState seed $ do
        a <- genP 0 5
        b <- mutate a
        c <- genP 0 4
        pure (a, b, c)
      cases = map trial [1 .. 4000]
  rs <- forM cases $ \(a, b, c) -> case (normalise a, normalise b, normalise c) of
    (Right na, Right nb, Right nc) -> do
      unless (equivRaw a b) (Left ("rewrite broke brute-force congruence:\n" ++ show a ++ "\n" ++ show b))
      unless (na == nb) (Left ("congruent terms with different normal forms:\n" ++ show a ++ "\n" ++ show b))
      unless (equivRaw a c == (na == nc)) (Left ("normal forms and brute force disagree:\n" ++ show a ++ "\n" ++ show c))
      Right (1 :: Int, if na == nc then 1 else 0 :: Int)
    _ -> Right (0, 0)
  Right (show (sum (map fst rs)) ++ " well-sorted cases, " ++ show (sum (map snd rs)) ++ " accidental equalities")

v1bool :: Check
v1bool = pure $ do
  -- exhaustive over all Boolean functions of up to 3 variables, built two ways
  let vars = [0, 1, 2]
      fromTable t = foldr (RBin BOr) (RBool False)
        [ foldr (RBin BAnd) (RBool True) [if testBit r j then RDrop (RV v) else RNot (RDrop (RV v)) | (j, v) <- zip [0 ..] vars]
        | r <- [0 .. 7 :: Int], testBit (t :: Int) r ]
      nfs = map (normalise . fromTable) [0 .. 255]
  unless (all (not . isLeft) nfs) (Left "a 3-variable function failed to normalise")
  unless (length (nub nfs) == 256) (Left "two distinct 3-variable functions share a normal form")
  -- the same function through De Morgan duals must give the same form
  let dual t = RNot (fromTable (complement t .&. 255))
  unless (and [normalise (dual t) == normalise (fromTable t) | t <- [0 .. 255]]) (Left "dual construction differs")
  Right "256 functions, exhaustive"

v3 :: Check
v3 = pure $ do
  let trial seed = flip evalState seed $ (,) <$> genP 0 5 <*> (genP 0 5 >>= mutate)
      m0 = load defaultParams { heapCap = 100000 } 1 [] nil
      procs = [p | (a, b) <- map trial [1 .. 600], r <- [a, b], Right p <- [normalise r]]
      act = forM procs $ \p -> do
        w <- internP p
        back <- readP w
        pure (p, w, back)
  case runMM act m0 of
    (Left f, _) -> Left ("fault while interning: " ++ show f)
    (Right rs, m) -> do
      unless (all (\(p, _, back) -> p == back) rs) (Left "readback of an interned term differs from the term")
      let ws = [(p, w) | (p, w, _) <- rs]
      unless (and [(p == q) == (w == v) | (p, w) <- take 300 ws, (q, v) <- take 300 ws])
        (Left "machine words are not equal exactly when normal forms are")
      case audit m of
        [] -> Right (show (length rs) ++ " terms, " ++ show (length (nub (map snd ws))) ++ " distinct words")
        vs -> Left (unlines vs)

-- | The machine's constructors must normalise on their own: interning raw
-- terms gives equal words exactly for congruent terms, and the readback is
-- the reference normal form.
v3raw :: Check
v3raw = pure $ do
  let trial seed = flip evalState seed $ do
        a <- genP 0 5
        b <- mutate a >>= mutate
        c <- genP 0 4
        pure (a, b, c)
      m0 = load defaultParams { heapCap = 200000 } 1 [] nil
      sameClass (Left (FaultSort _)) (Left (FaultSort _)) = True
      sameClass (Left (FaultWide _)) (Left (FaultWide _)) = True
      sameClass (Right p) (Right q) = p == q
      sameClass _ _ = False
      viaHeap r = fst (runMM (internRaw r >>= \w -> (,) w <$> readP w) m0)
  n <- fmap sum . forM (map trial [1 .. 3000]) $ \(a, b, c) -> do
    unless (sameClass (normalise a) (snd <$> viaHeap a))
      (Left ("machine normal form differs from the reference:\n" ++ show a))
    -- intern all three in one heap and compare words
    let act = (,,) <$> internRaw a <*> internRaw b <*> internRaw c
    case (normalise a, normalise b, normalise c, fst (runMM act m0)) of
      (Right na, Right _, Right nc, Right (wa, wb, wc)) -> do
        unless (wa == wb) (Left ("congruent raw terms interned to different words:\n" ++ show a ++ "\n" ++ show b))
        unless ((wa == wc) == (na == nc)) (Left ("words and normal forms disagree:\n" ++ show a ++ "\n" ++ show c))
        Right (1 :: Int)
      _ -> Right 0
  Right (show n ++ " triples of raw terms")

-- | Substitution on raw terms, with no normalisation: the textbook definition.
substRaw :: [RName] -> Int -> Raw -> Raw
substRaw env k = \case
  RNot a -> RNot (substRaw env k a)
  RBin op a b -> RBin op (substRaw env k a) (substRaw env k b)
  RRecv pers n pat b -> RRecv pers (substN n) pat (substRaw env (k + pVars pat) b)
  RSend n q -> RSend (substN n) (substRaw env k q)
  RPar a b -> RPar (substRaw env k a) (substRaw env k b)
  RDrop n -> RDrop (substN n)
  r -> r
  where
    substN (RV i) | i >= k = env !! (i - k)
    substN (RQ r) = RQ (substRaw env k r)
    substN n = n

-- | Instantiation commutes with normalisation, in the reference and in the
-- machine: substituting then normalising equals normalising then instantiating.
vInst :: Check
vInst = pure $ do
  let d = 3
      trial seed = flip evalState seed $ do
        r <- genP d 5
        boolEnv <- chance 70
        env <- replicateM d (if boolEnv then RQ . RBool <$> chance 50
                                        else oneOf [RQ (RBool True), RQ RNil, numeral 1, RQ (RSend (numeral 0) (RBool False))])
        pure (r, env)
      m0 = load defaultParams { heapCap = 200000 } 1 [] nil
      same (Left (FaultSort _)) (Left (FaultSort _)) = True
      same (Left (FaultWide _)) (Left (FaultWide _)) = True
      same (Right p) (Right q) = p == q
      same _ _ = False
  n <- fmap sum . forM (map trial [1 .. 4000]) $ \(r, env) -> do
    let expected = normalise (substRaw env 0 r)
        viaRef = do
          p <- normalise r
          ns <- mapM normName env
          inst ns 0 p
        viaHeap = fst . flip runMM m0 $ do
          w <- internRaw r
          ws <- mapM (\case RQ x -> internRaw x >>= \pw -> internN . mkQuote =<< readP pw
                            RV i -> pure (QV i)) env
          instPW ws 0 w >>= readP
    -- a term rejected before substitution may be accepted after it (a
    -- variable that made the term ill-sorted or too wide is gone): skip those
    -- Likewise a Boolean law can erase an ill-sorted operand before the
    -- substitution exposes it (*v xor *v is false whatever v is), so a sort
    -- fault in the substituted term need not survive: sort faults are
    -- detected only for operands that outlive normalisation.
    case (normalise r, expected) of
      (Left _, _) -> Right (0 :: Int)
      (_, Left (FaultSort _)) -> Right 0
      _ -> do
        unless (same expected viaRef) (Left ("reference instantiation differs from substitution:\n" ++ show r ++ "\n" ++ show env
                                             ++ "\n" ++ show expected ++ "\n" ++ show viaRef))
        unless (same expected viaHeap) (Left ("machine instantiation differs from substitution:\n" ++ show r ++ "\n" ++ show env))
        Right 1
  Right (show n ++ " open terms")

------------------------------------------------------------------------------
-- Matcher against the oracle

vMatch :: Check
vMatch = pure $ do
  let names seed = flip evalState seed $ do
        ps <- replicateM 6 (genP 0 3)
        pure ([NQ (PBool True), NQ (PBool False), NQ nil]
              ++ [mkQuote p | Right p <- map normalise ps]
              ++ [NQ (PSend c (PBool b)) | b <- [True, False], c <- [NQ nil, NQ (PBool True), NQ (PBool b)]]
              ++ [NQ (PSend (NQ (PBool b)) (PBool b')) | b <- [True, False], b' <- [True, False]])
      allNames = nub (concatMap names [1 .. 150])
      m0 = load defaultParams { heapCap = 100000 } 1 [] nil
  n <- fmap sum . forM testPats $ \pat -> fmap sum . forM allNames $ \nm -> do
    let viaOps = fmap (maybe [] (solutions pat)) (runPat pat nm)
        oracle = matchSpec pat nm
    unless (viaOps == oracle) (Left ("pattern program and oracle disagree on " ++ show (pSrc pat) ++ " against " ++ show nm))
    -- the machine's matcher, on heap words
    let act = do
          w <- internN nm
          hw <- runPatW pat w
          traverse (\(ss, mask) -> (\ns -> solutions pat (ns, mask)) <$> mapM readN ss) hw
        viaHeap = fmap (maybe [] id) (fst (runMM act m0))
    unless (viaHeap == oracle) (Left ("machine matcher and oracle disagree on " ++ show (pSrc pat) ++ " against " ++ show nm))
    Right (1 :: Int)
  Right (show n ++ " pattern/name pairs")

------------------------------------------------------------------------------
-- V5: the arbiter never prunes

v5 :: Check
v5 = pure $ do
  let witness n u = if u == 0 then 1 else fromIntegral ((toInteger u * 2 ^ (32 :: Int) + toInteger n - 1) `div` toInteger n) :: Word32
  unless (and [pick n (witness n u) == u | n <- [1 .. 64], u <- [0 .. n - 1]])
    (Left "some choice has no entropy witness")
  unless (and [nthSet m u == r | m <- [0x6, 0x9, 0x8000000000000001, maxBound], (u, r) <- zip [0 ..] [r | r <- [0 .. 63], testBit m r]])
    (Left "nthSet is wrong")
  let run = take 200000 (iterate lfsrStep 1)
  when (0 `elem` run) (Left "the LFSR reached zero")
  when (1 `elem` drop 1 run) (Left "the LFSR has a short cycle")
  Right "all n <= 64, all u < n"

------------------------------------------------------------------------------
-- V4: random programs under the step-refinement checker

genProgram :: Gen (String, [String])
genProgram = do
  k <- (+ 4) <$> below 6
  cs <- replicateM k component
  pure (concatMap (++ " | ") cs ++ "0", ["out"])
  where
    bch = oneOf ["b0", "b1", "b2"]
    kch = oneOf ["k0", "k1"]
    tgt = oneOf ["b0", "b1", "b2", "out", "out"]
    lit = oneOf ["true", "false"]
    arrow = (\p -> if p then " <= " else " <- ") <$> chance 15
    component = below 10 >>= \case
      0 -> (\c v -> c ++ "!(" ++ v ++ ")") <$> bch <*> lit
      1 -> (\c v -> c ++ "!(" ++ v ++ ")") <$> bch <*> lit
      2 -> (\c v -> c ++ "!(" ++ v ++ ")") <$> bch <*> lit
      3 -> gate
      4 -> gate
      5 -> gate
      6 -> (\c t v -> c ++ "!( " ++ t ++ "!(" ++ v ++ ") )") <$> kch <*> tgt <*> lit
      7 -> (\c b -> c ++ "!( for(a <- " ++ b ++ "){ out!(~*a) } )") <$> kch <*> bch
      8 -> (\c a body -> "for(v" ++ a ++ c ++ "){ " ++ body ++ " }") <$> kch <*> arrow <*> oneOf ["*v", "*v | *v", "*v | out!(true)"]
      _ -> (\c -> "for(@(c!(d)) <- " ++ c ++ "){ c!(*d) | out!(*d) }") <$> kch
    gate = do
      c <- bch
      a <- arrow
      (pat, exprs) <- oneOf
        [ ("a", ["*a", "~*a", "*a xor true"])
        , ("@(p && q)", ["*p", "*q", "*p xor *q", "*p || *q"])
        , ("@(p xor q)", ["*p", "*q", "*p && *q"])
        , ("@(~p)", ["*p", "~*p"])
        , ("@(p || q)", ["*p && *q", "*p"])
        , ("@true", ["true"]), ("@false", ["false"])
        , ("@(p && ~p)", ["*p"]) ]
      nest <- chance 25
      body <- if nest && pat == "a"
        then (\c2 t -> "for(c <- " ++ c2 ++ "){ " ++ t ++ "!(*a && *c) }") <$> bch <*> tgt
        else do
          n <- (+ 1) <$> below 2
          parts <- replicateM n ((\t e -> t ++ "!(" ++ e ++ ")") <$> tgt <*> oneOf exprs)
          pure (foldr1 (\x y -> x ++ " | " ++ y) parts)
      pure ("for(" ++ pat ++ a ++ c ++ "){ " ++ body ++ " }")

isResource :: Maybe Fault -> Bool
isResource = \case
  Just FaultStore -> True
  Just FaultHeap -> True
  Just FaultStack -> True
  _ -> False

v4 :: Check
v4 = pure $ do
  let progs = [evalState genProgram s | s <- [1 .. 400]]
  rs <- forM (zip [1 :: Int ..] progs) $ \(i, (src, ports)) -> forM [1, 2, 3] $ \seed ->
    case runSrc defaultParams src ports (fromIntegral (i * 7 + seed)) 80 of
      Left err -> Left ("program " ++ show i ++ ", seed " ++ show seed ++ ":\n" ++ src ++ "\n" ++ err)
      Right (o, _) -> do
        unless (oFault o == Nothing || isResource (oFault o))
          (Left ("program " ++ show i ++ " raised " ++ show (oFault o) ++ ":\n" ++ src))
        Right (oSteps o, if oQuiet o then 1 else 0 :: Int, if isResource (oFault o) then 1 else 0 :: Int)
  let flat = concat rs
  Right (show (length flat) ++ " runs, " ++ show (sum [s | (s, _, _) <- flat]) ++ " steps checked, "
         ++ show (sum [q | (_, q, _) <- flat]) ++ " quiescent, " ++ show (sum [f | (_, _, f) <- flat]) ++ " hit a resource bound")

-- | The same random programs on a deliberately tiny machine: resource faults
-- must be detected, never silent, and never a discrepancy.
v4small :: Check
v4small = pure $ do
  let tiny = Params { nS = 4, nR = 4, heapCap = 24, envMax = 3, stackMax = 4 }
      progs = [evalState genProgram s | s <- [1000 .. 1200]]
  rs <- forM (zip [1 :: Int ..] progs) $ \(i, (src, ports)) ->
    case runSrc tiny src ports (fromIntegral i) 60 of
      Left err -> Left ("program " ++ show i ++ ":\n" ++ src ++ "\n" ++ err)
      Right (o, _) -> do
        unless (oFault o == Nothing || isResource (oFault o)) (Left ("program " ++ show i ++ " raised " ++ show (oFault o)))
        Right (if isResource (oFault o) then 1 else 0 :: Int)
  Right (show (length rs) ++ " runs, " ++ show (sum rs) ++ " ended in a detected resource fault")

------------------------------------------------------------------------------
-- V6: every reference transition is taken under some seed

refGraph :: Proc -> Either String (S.Set (Proc, Proc))
refGraph p0 = go S.empty S.empty [p0]
  where
    go _ ts [] = Right ts
    go seen ts (p : ps)
      | p `S.member` seen = go seen ts ps
      | S.size seen > 500 = Left "reference graph too large for the coverage test"
      | otherwise = case redexes p of
          Left f -> Left (show f)
          Right rs -> let qs = map snd rs
                      in go (S.insert p seen) (foldr (\q -> S.insert (p, q)) ts qs) (qs ++ ps)

v6 :: Check
v6 = pure $ do
  let progs =
        [ "for(@(p xor q) <- x){ l!(*p) | r!(*q) } | x!(true)"
        , "for(@(p && q) <- x){ l!(*p) | r!(*q) } | x!(false)"
        , "for(@(p || q) <- x){ l!(*p) | r!(*q) } | x!(true) | x!(false)"
        , "for(a <- x){ l!(true) } | for(a <- x){ l!(false) } | x!(0)"
        , "for(a <- x){ for(b <- y){ z!(*a && *b) } } | x!(true) | x!(false) | y!(false) | y!(true)"
        , "for(a <= x){ y!(~*a) } | x!(true) | x!(false) | for(@(p xor q) <- y){ z!(*p) }"
        , "for(v <- k){ *v | *v } | k!( x!(true) ) | for(@(p || q) <- x){ l!(*p && *q) }"
        , "for(@(c!(p xor q)) <- k){ c!(*p) } | k!( x!(true) ) | k!( y!(false) )"
        , "for(@(p && q && r) <- x){ l!(*p xor *q xor *r) } | x!(false)" ]
  ns <- forM progs $ \src -> do
    let (p, _) = compileOrDie src
    ref <- refGraph p
    runs <- forM [1 .. 400] $ \seed -> rrStates <$> runChecked defaultParams seed [] p 100
    let taken = S.fromList [(a, b) | sts <- runs, (a, b) <- zip sts (drop 1 sts)]
    unless (taken `S.isSubsetOf` ref) (Left ("the machine took a transition the reference does not have:\n" ++ src))
    unless (ref `S.isSubsetOf` taken)
      (Left ("reference transitions never taken (" ++ show (S.size (ref `S.difference` taken)) ++ " of "
             ++ show (S.size ref) ++ "):\n" ++ src))
    Right (S.size ref)
  Right (show (sum ns) ++ " reference transitions, all taken, across " ++ show (length progs) ++ " programs")

------------------------------------------------------------------------------
-- V7: replay

v7 :: Check
v7 = pure $ do
  let progs = take 120 [evalState genProgram s | s <- [5000 ..]]
  n <- fmap sum . forM (zip [1 :: Word32 ..] progs) $ \(i, (src, ports)) -> do
    let (p, syms) = compileOrDie src
        eg = mapMaybe (symName syms) ports
    rr <- runChecked defaultParams i eg p 60
    -- replay on a machine with a different seed: entropy must not matter
    let (evs0, m0) = takeEvents (load defaultParams (i + 12345) eg p)
        stepR (m, _) d = takeEvents' (replayM d m)
        takeEvents' m = let (evs, m') = takeEvents m in (m', evs)
        trace = scanl stepR (m0, evs0) (rrDecisions rr)
        decodeEg (m, evs) = firstLeft
          [ either (Left . show) Right (fst (runMM (PSend <$> readN c <*> readP q) m)) | EvEgress c q <- evs ]
    unless (all ((== Nothing) . fault . fst) trace) (Left ("replay faulted:\n" ++ src))
    sts <- firstLeft (map (either (Left . show) Right . alpha . fst) trace)
    unless (sts == rrStates rr) (Left ("replay diverged from the recorded run:\n" ++ src))
    egs <- concat <$> mapM decodeEg trace
    unless (egs == rrEgress rr) (Left ("replay egress differs:\n" ++ src))
    Right (length (rrDecisions rr))
  Right (show n ++ " steps replayed")

------------------------------------------------------------------------------
-- V9 (trace level): persistent receive against the reflective encoding

v9 :: Check
v9 = pure $ do
  let persistent = "for(a <= x){ out!(~*a) } | x!(true) | x!(false) | x!(true)"
      encoding = "n!( for(v <- n){ n!(*v) | *v } | for(a <- x){ out!(~*a) } ) | for(v <- n){ n!(*v) | *v }"
                 ++ " | x!(true) | x!(false) | x!(true)"
  (o1, _) <- runSrc defaultParams persistent ["out"] 1 200
  unless (oQuiet o1) (Left "the persistent version did not reach quiescence")
  rs <- forM [1 .. 40] $ \seed -> do
    (o2, _) <- runSrc defaultParams encoding ["out"] seed 400
    -- the encoding unfolds for ever, so it ends on the receive-table bound
    unless (oFault o2 == Just FaultStore) (Left ("encoding: expected the store bound, got " ++ show (oFault o2)))
    unless (oEgress o2 == oEgress o1) (Left ("encoding egress " ++ show (oEgress o2) ++ " differs from " ++ show (oEgress o1)))
    Right (oSteps o2)
  Right ("same egress " ++ show (oEgress o1) ++ "; persistent " ++ show (oSteps o1) ++ " steps, encoding "
         ++ show (minimum rs) ++ "-" ++ show (maximum rs) ++ " steps to the store bound")

------------------------------------------------------------------------------
-- Directed programs (spec, Section 8.5)

adder :: Check
adder = pure $ do
  let b v = if v then "true" else "false"
      half x y = "for(a <- x){ for(b <- y){ s!(*a xor *b) | c!(*a && *b) } } | x!(" ++ b x ++ ") | y!(" ++ b y ++ ")"
      full x y z = "for(a <- x){ for(b <- y){ for(d <- z){ s!(*a xor *b xor *d) | c!((*a && *b) || (*d && (*a xor *b))) } } }"
                   ++ " | x!(" ++ b x ++ ") | y!(" ++ b y ++ ") | z!(" ++ b z ++ ")"
      bs = [False, True]
  _ <- forM [(x, y) | x <- bs, y <- bs] $ \(x, y) -> do
    (o, _) <- runSrc defaultParams (half x y) ["s", "c"] 3 50
    unless (oEgress o == sort ["s!(" ++ b (x /= y) ++ ")", "c!(" ++ b (x && y) ++ ")"]) (Left ("half adder wrong on " ++ show (x, y)))
    Right ()
  _ <- forM [(x, y, z) | x <- bs, y <- bs, z <- bs] $ \(x, y, z) -> do
    (o, _) <- runSrc defaultParams (full x y z) ["s", "c"] 5 50
    let total = length (filter id [x, y, z])
    unless (oEgress o == sort ["s!(" ++ b (odd total) ++ ")", "c!(" ++ b (total >= 2) ++ ")"]) (Left ("full adder wrong on " ++ show (x, y, z)))
    Right ()
  Right "4 + 8 input vectors"

negative :: Check
negative = pure $ do
  (o, _) <- runSrc defaultParams "for(a <- x){ out!(~*a) } | x!(0)" ["out"] 1 10
  unless (case oFault o of Just (FaultSort _) -> True; _ -> False) (Left ("expected a sort fault, got " ++ show (oFault o)))
  (o2, _) <- runSrc defaultParams "for(@(p && q) <- x){ out!(*p) } | x!(0)" ["out"] 1 10
  unless (case oFault o2 of Just (FaultSort _) -> True; _ -> False) (Left ("expected a sort fault at the leaf, got " ++ show (oFault o2)))
  unless (isLeft (compileSource "for(@(for(v <- x){ 0 }) <- y){ 0 }")) (Left "a receive pattern was accepted")
  unless (isLeft (compileSource "for(@(a && b && c && d && e && f && g) <- y){ 0 }")) (Left "a 7-variable pattern was accepted")
  unless (isLeft (compileSource "for(@(a && 0) <- y){ 0 }")) (Left "an ill-sorted pattern was accepted")
  unless (isLeft (compileSource "~(x!(0))")) (Left "an ill-sorted term was accepted")
  let wide = "for(a <- x){ for(b <- x){ for(c <- x){ for(d <- x){ for(e <- x){ for(f <- x){ for(g <- x){ "
             ++ "y!(*a xor *b xor *c xor *d xor *e xor *f xor *g) } } } } } } }"
  unless (isLeft (compileSource wide)) (Left "a 7-variable Boolean expression was accepted")
  Right "sort faults raised; malformed sources rejected"

ingressTest :: Check
ingressTest = pure $ do
  let (p, syms) = compileOrDie "for(a <= x){ out!(~*a) }"
      out = fromJust (symName syms "out")
      x = fromJust (symName syms "x")
      m0 = snd (takeEvents (load defaultParams 1 [out] p))
      (b0, m1) = stepM m0
      m2 = ingress x (PBool True) (snd (takeEvents m1))
      (b1, m3) = stepM m2
      outs = [() | EvEgress _ (WBool False) <- events m3]
      (b2, m4) = stepM (snd (takeEvents m3))
  unless (not b0 && quiescent m1) (Left "an idle machine was not quiescent")
  unless (b1 && length outs == 1) (Left "ingress did not produce the output")
  unless (not b2 && quiescent m4 && fault m4 == Nothing) (Left "the machine did not return to quiescence")
  unless (null (audit m4)) (Left (unlines (audit m4)))
  Right "idle, ingress, output, idle"

------------------------------------------------------------------------------

main :: IO ()
main = do
  fails <- newIORef 0
  let t = check fails
  putStrLn "Canonical forms"
  t "V1  normal forms decide congruence (random, against brute force)" v1
  t "V1  Boolean normal forms, exhaustive for k <= 3" v1bool
  t "V3  interner: equal words exactly for congruent terms" v3
  t "V3  interner normalises raw terms by its own constructors" v3raw
  t "    instantiation commutes with normalisation (reference and machine)" vInst
  putStrLn "Matching and choice"
  t "    pattern programs and machine matcher against the oracle" vMatch
  t "V5  arbiter: a witness for every choice" v5
  putStrLn "Directed programs"
  t "forwarder" (expectOutcomes "for(a <- x){ out!(*a) } | x!(true)" ["out"] [(["out!(true)"], "0")])
  t "AND gate (spec appendix)" (expectOutcomes "for(a <- x){ for(b <- y){ z!(*a && *b) } } | x!(true) | y!(false)" [] [([], "z!(false)")])
  t "XOR gate" (expectOutcomes "for(a <- x){ for(b <- y){ z!(*a xor *b) } } | x!(true) | y!(false)" ["z"] [(["z!(true)"], "0")])
  t "half and full adder" adder
  t "inverse XOR on true: two solutions, both reached"
    (expectOutcomes "for(@(p xor q) <- x){ l!(*p) | r!(*q) } | x!(true)" []
       [([], "l!(true) | r!(false)"), ([], "l!(false) | r!(true)")])
  t "inverse XOR on false: the equal pairs"
    (expectOutcomes "for(@(p xor q) <- x){ l!(*p) | r!(*q) } | x!(false)" []
       [([], "l!(true) | r!(true)"), ([], "l!(false) | r!(false)")])
  t "inverse AND on false: three solutions, all reached"
    (expectOutcomes "for(@(p && q) <- x){ l!(*p) | r!(*q) } | x!(false)" ["l", "r"]
       [(["l!(false)", "r!(false)"], "0"), (["l!(true)", "r!(false)"], "0"), (["l!(false)", "r!(true)"], "0")])
  t "unsatisfiable pattern: no redex, the send remains"
    (expectOutcomes "for(@(v && ~v) <- x){ out!(true) } | x!(true)" ["out"] [([], "x!(true) | for(@(b0 && ~b0) <- x){ out!(true) }")])
  t "two receivers, one send: both outcomes reached"
    (expectOutcomes "for(a <- x){ out!(true) } | for(a <- x){ out!(false) } | x!(0)" ["out"]
       [(["out!(true)"], "for(s0 <- x){ out!(false) }"), (["out!(false)"], "for(s0 <- x){ out!(true) }")])
  t "equal names, different syntax"
    (expectOutcomes "for(v <- @(true && false)){ out!(*v) } | @false!(true)" ["out"] [(["out!(true)"], "0")])
  t "general drop of quoted code"
    (expectOutcomes "for(v <- k){ *v | *v } | k!( out!(true) )" ["out"] [(["out!(true)", "out!(true)"], "0")])
  t "deep send pattern"
    (expectOutcomes "for(@(c!(d)) <- k){ c!(*d) } | k!( out!(false) )" ["out"] [(["out!(false)"], "0")])
  t "top-level Booleans are kept in the residue"
    (expectOutcomes "for(a <- x){ *a | ~*a } | x!(true)" [] [([], "false | true")])
  t "partial instantiation renormalises open Boolean code"
    (expectOutcomes ("for(a <- x){ @(for(b <- y){ out!(*a && *b) })!(true) } | x!(false)"
                     ++ " | for(v <- @(for(b <- y){ out!(false) })){ out!(*v) }") ["out"] [(["out!(true)"], "0")])
  t "persistent receive"
    (expectOutcomes "for(a <= x){ out!(~*a) } | x!(true) | x!(false)" ["out"] [(["out!(false)", "out!(true)"], "for(s0 <= x){ out!(bfn[0]#1) }")])
  t "ingress and egress at the boundary" ingressTest
  t "negative tests: sort faults and rejected sources" negative
  putStrLn "Refinement"
  t "V4  random programs under the step-refinement checker" v4
  t "V4  the same on a tiny machine: resource faults are detected" v4small
  t "V6  redex coverage: every reference transition is taken" v6
  t "V7  replay from the decision log" v7
  t "V9  persistent receive against the reflective encoding (egress traces)" v9
  n <- readIORef fails
  if n == 0 then putStrLn "\nall checks passed" else putStrLn ("\n" ++ show n ++ " check(s) FAILED") >> exitFailure
