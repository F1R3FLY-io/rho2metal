{-# LANGUAGE LambdaCase #-}
-- | Core terms, canonical forms, matching and the reference reduction relation.
--
-- This module is the executable semantics (spec, Sections 3 and 4).  Everything
-- else in the library is checked against it.
module Rho.Core
  ( -- * Limits and faults
    kMax, Fault(..)
    -- * Boolean functions (truth tables over an ordered support)
  , BF(..), bfConst, bfVar, bfNot, bfBin, minimise, restrict, fromBF, toBF
    -- * Raw (de Bruijn, un-normalised) and normal-form terms
  , Raw(..), RName(..), Proc(..), Name(..), nil, mkPar, mkDrop, mkQuote, comps
  , normalise, normName
    -- * Patterns
  , POp(..), VRef(..), BExp(..), SP(..), SD(..), Pat(..), pVars, mkPat, validMask, ttOf, evalB
  , runPat, solutions, matchSpec
    -- * Scoping from surface syntax
  , scope, compilePtrn, numeral, numeralOf
    -- * Substitution and reduction
  , inst, Redex(..), redexes
    -- * Printing
  , ppProc, ppName
  ) where

import Control.Monad (foldM, forM)
import Data.Bits
import Data.List (elemIndex, intercalate, sort, union)
import qualified Data.Map.Strict as M
import Data.Word (Word64)
import Numeric (showHex)

import Rho.Syntax

-- | Maximum Boolean support, and maximum Boolean variables in one pattern (D12).
kMax :: Int
kMax = 6

data Fault
  = FaultSort String      -- ^ a Boolean operand or Boolean leaf met a non-Boolean
  | FaultWide Int         -- ^ Boolean support above 'kMax' (compile-time rejection)
  | FaultHeap | FaultStore | FaultStack
  | FaultInternal String
  deriving (Eq, Show)

------------------------------------------------------------------------------
-- Boolean functions

-- | A Boolean function: ascending support (variable indices) and a truth table
-- in which bit @r@ is the value at the assignment "variable at position i takes
-- bit i of r".
data BF = BF [Int] Integer deriving (Eq, Show)

tableOf :: Int -> (Int -> Bool) -> Integer
tableOf k f = foldl (\acc r -> if f r then setBit acc r else acc) 0 [0 .. bit k - 1]

bfConst :: Bool -> BF
bfConst b = BF [] (if b then 1 else 0)

bfVar :: Int -> BF
bfVar i = BF [i] 2

expandTo :: [Int] -> BF -> Integer
expandTo sup' (BF sup t) = tableOf (length sup') (testBit t . proj)
  where
    pos = [p | v <- sup, Just p <- [elemIndex v sup']]
    proj r = foldl (.|.) 0 [bit j | (j, p) <- zip [0 ..] pos, testBit r p]

bfNot :: BF -> BF
bfNot (BF s t) = BF s (complement t .&. (bit (bit (length s)) - 1))

bfBin :: BOp -> BF -> BF -> BF
bfBin op a@(BF sa _) b@(BF sb _) = minimise (BF s (f (expandTo s a) (expandTo s b)))
  where
    s = sort (sa `union` sb)
    f = case op of BAnd -> (.&.); BOr -> (.|.); BXor -> xor

-- | Remove the variables the function does not depend on.
minimise :: BF -> BF
minimise bf@(BF s t) = case [p | p <- [0 .. length s - 1], not (depends p)] of
  [] -> bf
  (p : _) -> minimise (restrict p False bf)
  where
    depends p = any (\r -> not (testBit r p) && testBit t r /= testBit t (setBit r p))
                    [0 .. bit (length s) - 1 :: Int]

-- | Fix the variable at support position @p@ to @b@ (a cofactor).
restrict :: Int -> Bool -> BF -> BF
restrict p b (BF s t) = BF (take p s ++ drop (p + 1) s) (tableOf (length s - 1) (testBit t . ins))
  where
    ins r = ((r `shiftR` p) `shiftL` (p + 1)) .|. (r .&. (bit p - 1)) .|. (if b then bit p else 0)

------------------------------------------------------------------------------
-- Terms

-- | Un-normalised terms with de Bruijn indices for the variable category.
data Raw
  = RNil | RBool Bool | RNot Raw | RBin BOp Raw Raw
  | RRecv Bool RName Pat Raw | RSend RName Raw | RPar Raw Raw | RDrop RName
  deriving (Eq, Show)

data RName = RQ Raw | RV Int deriving (Eq, Show)

-- | Normal forms (spec, Section 4).  Invariants: 'PPar' holds a sorted list of
-- length other than one with no nested 'PPar'; 'PBfn' has minimal ascending
-- support of size 1..6 and is neither constant nor a projection.
data Proc
  = PPar [Proc] | PBool Bool | PSend Name Proc | PRecv Bool Name Pat Proc
  | PDrop Int | PBfn [Int] Word64
  deriving (Eq, Ord, Show)

-- | Names.  Invariant: never @NQ (PDrop i)@, which is @NVar i@.
data Name = NQ Proc | NVar Int deriving (Eq, Ord, Show)

nil :: Proc
nil = PPar []

comps :: Proc -> [Proc]
comps (PPar ps) = ps
comps p = [p]

mkPar :: [Proc] -> Proc
mkPar ps = case sort (concatMap comps ps) of
  [p] -> p
  qs -> PPar qs

mkDrop :: Name -> Proc
mkDrop (NQ p) = p
mkDrop (NVar i) = PDrop i

mkQuote :: Proc -> Name
mkQuote (PDrop i) = NVar i
mkQuote p = NQ p

fromBF :: BF -> Either Fault Proc
fromBF bf = case minimise bf of
  BF [] t -> Right (PBool (t == 1))
  BF [i] 2 -> Right (PDrop i)
  BF s t
    | length s > kMax -> Left (FaultWide (length s))
    | otherwise -> Right (PBfn s (fromInteger t))

toBF :: Proc -> Either Fault BF
toBF = \case
  PBool b -> Right (bfConst b)
  PDrop i -> Right (bfVar i)
  PBfn s t -> Right (BF s (toInteger t))
  p -> Left (FaultSort ("non-Boolean operand " ++ take 60 (show p)))

normalise :: Raw -> Either Fault Proc
normalise = \case
  RNil -> Right nil
  RBool b -> Right (PBool b)
  RNot a -> normalise a >>= toBF >>= fromBF . bfNot
  RBin op a b -> do
    x <- normalise a >>= toBF
    y <- normalise b >>= toBF
    fromBF (bfBin op x y)
  RRecv pers n pat b -> PRecv pers <$> normName n <*> pure pat <*> normalise b
  RSend n q -> PSend <$> normName n <*> normalise q
  RPar a b -> (\x y -> mkPar [x, y]) <$> normalise a <*> normalise b
  RDrop n -> mkDrop <$> normName n

normName :: RName -> Either Fault Name
normName (RQ r) = mkQuote <$> normalise r
normName (RV i) = Right (NVar i)

------------------------------------------------------------------------------
-- Patterns

-- | Pattern-program operations (spec, Section 5.5).  The program ends when the
-- operations are exhausted, at which point the cursor stack must be empty.
data POp = NBind | NEq Int | QZeroOp | QSendOp | BLeaf Word64 deriving (Eq, Ord, Show)

-- | A pattern variable: structural (index into the bindings) or Boolean
-- (position in the mask space).
data VRef = VS Int | VB Int deriving (Eq, Ord, Show)

data BExp = BC Bool | BV Int | BN BExp | BB BOp BExp BExp deriving (Eq, Ord, Show)
data SP = SPVar VRef | SPQ SD deriving (Eq, Ord, Show)
data SD = SDNil | SDVar VRef | SDSend SP SD | SDBool BExp deriving (Eq, Ord, Show)

-- | A compiled pattern.  'pSrc' is the source form, kept for the matching
-- oracle; equality is on the program, as the spec requires.
data Pat = Pat { pOps :: [POp], pNS :: Int, pNB :: Int, pSrc :: SP } deriving (Show)

patKey :: Pat -> ([POp], Int, Int)
patKey p = (pOps p, pNS p, pNB p)
instance Eq Pat where a == b = patKey a == patKey b
instance Ord Pat where compare a b = compare (patKey a) (patKey b)

pVars :: Pat -> Int
pVars p = pNS p + pNB p

validMask :: Int -> Word64
validMask nb = if nb >= 6 then maxBound else bit (bit nb) - 1

evalB :: BExp -> Int -> Bool
evalB e r = case e of
  BC b -> b
  BV j -> testBit r j
  BN a -> not (evalB a r)
  BB BAnd a b -> evalB a r && evalB b r
  BB BOr a b -> evalB a r || evalB b r
  BB BXor a b -> evalB a r /= evalB b r

ttOf :: Int -> BExp -> Word64
ttOf nb e = foldl (\a r -> if evalB e r then setBit a r else a) 0 [0 .. bit nb - 1]

-- | Build a pattern from its source form.  Structural variables must be
-- numbered in order of first occurrence in program order.
mkPat :: Int -> Int -> SP -> Pat
mkPat ns nb sp = Pat (fst (go sp 0)) ns nb sp
  where
    go (SPVar v) n = var v n
    go (SPQ d) n = goD d n
    goD SDNil n = ([QZeroOp], n)
    goD (SDVar v) n = var v n
    goD (SDBool e) n = ([BLeaf (ttOf nb e)], n)
    goD (SDSend c d) n = let (a, n1) = go c n; (b, n2) = goD d n1 in (QSendOp : a ++ b, n2)
    var (VS i) n | i == n = ([NBind], n + 1)
                 | otherwise = ([NEq i], n)
    var (VB j) n = ([BLeaf (ttOf nb (BV j))], n)

sortFaultLeaf :: Fault
sortFaultLeaf = FaultSort "Boolean leaf met a non-Boolean name"

-- | Run a pattern program on a closed name.  @Nothing@ is a structural
-- mismatch; otherwise the structural bindings and the solution mask.
runPat :: Pat -> Name -> Either Fault (Maybe ([Name], Word64))
runPat pat n0 = go (pOps pat) [n0] [] (validMask (pNB pat))
  where
    go [] [] bs m = Right (Just (reverse bs, m))
    go [] _ _ _ = Left (FaultInternal "pattern program left the cursor stack non-empty")
    go _ [] _ _ = Left (FaultInternal "pattern program ran out of cursor stack")
    go (op : ops) (n : st) bs m = case op of
      NBind -> go ops st (n : bs) m
      NEq i -> if reverse bs !! i == n then go ops st bs m else Right Nothing
      QZeroOp -> if n == NQ nil then go ops st bs m else Right Nothing
      QSendOp -> case n of
        NQ (PSend c q) -> go ops (c : mkQuote q : st) bs m
        _ -> Right Nothing
      BLeaf t -> case n of
        NQ (PBool b) -> go ops st bs (m .&. (if b then t else complement t))
        _ -> Left sortFaultLeaf

-- | The substitutions denoted by a successful run: one per set bit of the
-- mask, each tagged with its row.  Values are listed structural first.
solutions :: Pat -> ([Name], Word64) -> [(Int, [Name])]
solutions pat (structs, mask) =
  [ (r, structs ++ [NQ (PBool (testBit r j)) | j <- [0 .. pNB pat - 1]])
  | r <- [0 .. bit (pNB pat) - 1], testBit mask r ]

-- | The matching oracle: the match set of Definition 1, computed from the
-- source pattern by enumeration, without pattern programs or masks.
matchSpec :: Pat -> Name -> Either Fault [(Int, [Name])]
matchSpec pat n0 = do
  r <- walk (pSrc pat) n0 (M.empty, [])
  Right $ case r of
    Nothing -> []
    Just (bs, cs) ->
      [ (row, [bs M.! i | i <- [0 .. pNS pat - 1]] ++ [NQ (PBool (testBit row j)) | j <- [0 .. pNB pat - 1]])
      | row <- [0 .. bit (pNB pat) - 1], all (\(e, b) -> evalB e row == b) cs ]
  where
    walk (SPVar v) n st = bindv v n st
    walk (SPQ d) n st = case n of
      NQ p -> walkD d p st
      NVar _ -> Left (FaultInternal "open name in a match")
    walkD SDNil p st = Right (if p == nil then Just st else Nothing)
    walkD (SDVar v) p st = bindv v (mkQuote p) st
    walkD (SDBool e) p (bs, cs) = case p of
      PBool b -> Right (Just (bs, (e, b) : cs))
      _ -> Left sortFaultLeaf
    walkD (SDSend c d) p st = case p of
      PSend c' q -> walk c c' st >>= maybe (Right Nothing) (walkD d q)
      _ -> Right Nothing
    bindv (VS i) n (bs, cs) = Right $ case M.lookup i bs of
      Nothing -> Just (M.insert i n bs, cs)
      Just n' -> if n == n' then Just (bs, cs) else Nothing
    bindv (VB j) n (bs, cs) = case n of
      NQ (PBool b) -> Right (Just (bs, (BV j, b) : cs))
      _ -> Left sortFaultLeaf

------------------------------------------------------------------------------
-- Scoping

-- | The k-th symbol name: @\@0@, @\@(\@0!(0))@, ...  Free identifiers of a
-- program are mapped to these, in order of first occurrence.
numeral :: Int -> RName
numeral 0 = RQ RNil
numeral k = RQ (RSend (numeral (k - 1)) RNil)

numeralOf :: Name -> Maybe Int
numeralOf (NQ (PPar [])) = Just 0
numeralOf (NQ (PSend n (PPar []))) = (+ 1) <$> numeralOf n
numeralOf _ = Nothing

-- | Compile a surface pattern.  Returns the pattern and its variables in
-- binding order (structural first, then Boolean).
compilePtrn :: SPtrn -> Either String (Pat, [String])
compilePtrn pt = do
  mapM_ checkOps (opTrees pt)
  let bvars = dedup (concatMap dvars (opTrees pt))
  (sp, (ss, bs)) <- goP bvars pt ([], [])
  if length bs > kMax
    then Left ("pattern has " ++ show (length bs) ++ " Boolean variables; the limit is " ++ show kMax)
    else Right (mkPat (length ss) (length bs) sp, ss ++ bs)
  where
    dedup = foldl (\acc x -> if x `elem` acc then acc else acc ++ [x]) []
    -- maximal operator subtrees
    opTrees (PtVar _) = []
    opTrees (PtQuote d) = opTreesD d
    opTreesD d = case d of
      DNot _ -> [d]
      DBin {} -> [d]
      DSend p e -> opTrees p ++ opTreesD e
      _ -> []
    dvars d = case d of
      DVar w -> [w]
      DNot a -> dvars a
      DBin _ a b -> dvars a ++ dvars b
      _ -> []
    checkOps d = case d of
      DNot a -> checkOps a
      DBin _ a b -> checkOps a >> checkOps b
      DBool _ -> Right ()
      DVar _ -> Right ()
      _ -> Left "ill-sorted pattern: a non-Boolean pattern under a Boolean operator"
    ref bvars w (ss, bs)
      | w `elem` bvars = case elemIndex w bs of
          Just j -> (VB j, (ss, bs))
          Nothing -> (VB (length bs), (ss, bs ++ [w]))
      | otherwise = case elemIndex w ss of
          Just i -> (VS i, (ss, bs))
          Nothing -> (VS (length ss), (ss ++ [w], bs))
    goP bvars (PtVar w) st = let (v, st') = ref bvars w st in Right (SPVar v, st')
    goP bvars (PtQuote d) st = goD bvars d st >>= \(sd, st') -> Right (SPQ sd, st')
    goD bvars d st = case d of
      DNil -> Right (SDNil, st)
      DBool b -> Right (SDBool (BC b), st)
      DVar w -> let (v, st') = ref bvars w st in Right (SDVar v, st')
      DSend p e -> do
        (sp, st1) <- goP bvars p st
        (sd, st2) <- goD bvars e st1
        Right (SDSend sp sd, st2)
      _ -> let (e, st') = goB bvars d st in Right (SDBool e, st')
    goB bvars d st = case d of
      DBool b -> (BC b, st)
      DVar w -> case ref bvars w st of
        (VB j, st') -> (BV j, st')
        (VS _, st') -> (BC False, st')   -- unreachable: operator variables are Boolean
      DNot a -> let (x, st') = goB bvars a st in (BN x, st')
      DBin op a b -> let (x, st1) = goB bvars a st; (y, st2) = goB bvars b st1 in (BB op x y, st2)
      _ -> (BC False, st)                -- unreachable after checkOps

-- | Resolve identifiers.  Returns the term and the symbol table (free
-- identifiers, in order; the k-th is the name @numeral k@).
scope :: SProc -> Either String (Raw, [String])
scope p0 = goP [] p0 []
  where
    goP env p syms = case p of
      SNil -> Right (RNil, syms)
      SBool b -> Right (RBool b, syms)
      SNot a -> goP env a syms >>= \(x, s) -> Right (RNot x, s)
      SBin op a b -> do
        (x, s1) <- goP env a syms
        (y, s2) <- goP env b s1
        Right (RBin op x y, s2)
      SPar a b -> do
        (x, s1) <- goP env a syms
        (y, s2) <- goP env b s1
        Right (RPar x y, s2)
      SDrop n -> goN env n syms >>= \(x, s) -> Right (RDrop x, s)
      SSend n q -> do
        (x, s1) <- goN env n syms
        (y, s2) <- goP env q s1
        Right (RSend x y, s2)
      SFor pers pt n b -> do
        (x, s1) <- goN env n syms
        (pat, vs) <- compilePtrn pt
        (y, s2) <- goP (reverse vs ++ env) b s1
        Right (RRecv pers x pat y, s2)
    goN env n syms = case n of
      SQuote p -> goP env p syms >>= \(x, s) -> Right (RQ x, s)
      SId w -> case elemIndex w env of
        Just i -> Right (RV i, syms)
        Nothing -> case elemIndex w syms of
          Just k -> Right (numeral k, syms)
          Nothing -> Right (numeral (length syms), syms ++ [w])

------------------------------------------------------------------------------
-- Substitution and reduction

-- | @inst env k p@ substitutes the closed names @env@ for the free variables
-- of @p@ that lie beyond @k@ enclosing binders.  @env@ is listed from the
-- most recently bound.  The result is in normal form.
inst :: [Name] -> Int -> Proc -> Either Fault Proc
inst env = go
  where
    look i k
      | i - k < length env = Right (env !! (i - k))
      | otherwise = Left (FaultInternal "variable beyond the environment")
    go k = \case
      PPar ps -> mkPar <$> mapM (go k) ps
      PBool b -> Right (PBool b)
      PSend n q -> PSend <$> goN k n <*> go k q
      PRecv pers n pat b -> PRecv pers <$> goN k n <*> pure pat <*> go (k + pVars pat) b
      PDrop i | i < k -> Right (PDrop i)
              | otherwise -> mkDrop <$> look i k
      PBfn s t -> do
        let step bf (p, v)
              | v < k = Right bf
              | otherwise = look v k >>= \case
                  NQ (PBool b) -> Right (restrict p b bf)
                  _ -> Left (FaultSort "Boolean operand met a non-Boolean name")
        bf <- foldM step (BF s (toInteger t)) (reverse (zip [0 ..] s))
        fromBF bf
    goN k = \case
      NVar i | i < k -> Right (NVar i)
             | otherwise -> look i k
      NQ p -> mkQuote <$> go k p

-- | A redex: the indices of the send and the receive among the top-level
-- components, and the solution row.
data Redex = Redex { rxSend :: Int, rxRecv :: Int, rxRow :: Int } deriving (Eq, Ord, Show)

-- | Every redex of a closed process with its reduct (rules COMM and COMM!).
redexes :: Proc -> Either Fault [(Redex, Proc)]
redexes p = fmap concat . sequence $
  [ do sols <- matchSpec pat (mkQuote q)
       forM sols $ \(row, vals) -> do
         r <- inst (reverse vals) 0 body
         Right (Redex i j row, mkPar (r : [x | (k, x) <- ics, k /= i, pers || k /= j]))
  | (i, PSend c q) <- ics, (j, PRecv pers c' pat body) <- ics, c == c' ]
  where ics = zip [0 :: Int ..] (comps p)

------------------------------------------------------------------------------
-- Printing

ppName :: [String] -> Name -> String
ppName syms n = case numeralOf n of
  Just k | k < length syms -> syms !! k
  _ -> case n of
    NVar i -> "_" ++ show i
    NQ p -> "@" ++ atom syms p

atom :: [String] -> Proc -> String
atom syms p = case p of
  PPar [] -> "0"
  PBool _ -> ppProc syms p
  _ -> "(" ++ ppProc syms p ++ ")"

ppProc :: [String] -> Proc -> String
ppProc syms = \case
  PPar [] -> "0"
  PPar ps -> intercalate " | " (map (ppProc syms) ps)
  PBool b -> if b then "true" else "false"
  PSend n q -> ppName syms n ++ "!(" ++ ppProc syms q ++ ")"
  PRecv pers n pat b ->
    "for(" ++ ppSP (pSrc pat) ++ (if pers then " <= " else " <- ") ++ ppName syms n ++ "){ " ++ ppProc syms b ++ " }"
  PDrop i -> "*_" ++ show i
  PBfn s t -> "bfn" ++ show s ++ "#" ++ showHex t ""
  where
    ppV (VS i) = "s" ++ show i
    ppV (VB j) = "b" ++ show j
    ppSP (SPVar v) = ppV v
    ppSP (SPQ d) = "@" ++ ppSD d
    ppSD SDNil = "0"
    ppSD (SDVar v) = ppV v
    ppSD (SDSend c d) = "(" ++ ppSP c ++ "!(" ++ ppSD d ++ "))"
    ppSD (SDBool e) = case e of
      BN _ -> "(" ++ ppB e ++ ")"
      _ -> ppB e
    ppB (BC b) = if b then "true" else "false"
    ppB (BV j) = "b" ++ show j
    ppB (BN a) = "~" ++ ppB a
    ppB (BB op a b) = "(" ++ ppB a ++ opS op ++ ppB b ++ ")"
    opS BAnd = " && "
    opS BOr = " || "
    opS BXor = " xor "
