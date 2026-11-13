-- | Surface syntax and parser for the source calculus (spec, Section 3.1).
module Rho.Syntax
  ( SProc(..), SName(..), SPtrn(..), SDP(..), BOp(..), parseProgram
  ) where

import Data.Char (isAlpha, isAlphaNum, isSpace)

data BOp = BAnd | BOr | BXor deriving (Eq, Ord, Show)

data SProc
  = SNil | SBool Bool | SNot SProc | SBin BOp SProc SProc
  | SFor Bool SPtrn SName SProc      -- ^ True = persistent receive (<=)
  | SSend SName SProc | SPar SProc SProc | SDrop SName
  deriving (Eq, Show)

data SName = SQuote SProc | SId String deriving (Eq, Show)
data SPtrn = PtVar String | PtQuote SDP deriving (Eq, Show)
data SDP = DNil | DBool Bool | DVar String | DSend SPtrn SDP | DNot SDP | DBin BOp SDP SDP
  deriving (Eq, Show)

data Tok = TId String | TZero | TSym String deriving (Eq, Show)

keywords :: [String]
keywords = ["true", "false", "xor", "for"]

lexer :: String -> Either String [Tok]
lexer [] = Right []
lexer s@(c : cs)
  | isSpace c = lexer cs
  | c == '/', ('/' : _) <- cs = lexer (dropWhile (/= '\n') cs)
  | isAlpha c || c == '_' =
      let (w, r) = span (\x -> isAlphaNum x || x == '_' || x == '\'') s in (TId w :) <$> lexer r
  | c == '0' = (TZero :) <$> lexer cs
  | otherwise = case [t | t <- syms, take (length t) s == t] of
      (t : _) -> (TSym t :) <$> lexer (drop (length t) s)
      [] -> Left ("unexpected character " ++ show c)
  where syms = ["<-", "<=", "&&", "||", "(", ")", "{", "}", "!", "*", "@", "~", "|"]

type P a = [Tok] -> Either String (a, [Tok])

ctx :: [Tok] -> String
ctx ts = if null ts then "end of input" else show (take 4 ts)

expect :: String -> [Tok] -> Either String [Tok]
expect s (TSym t : r) | t == s = Right r
expect s ts = Left ("expected " ++ show s ++ " at " ++ ctx ts)

chain :: (Tok -> Bool) -> (a -> a -> a) -> P a -> P a
chain isOp f sub ts = sub ts >>= uncurry go
  where go a (t : r) | isOp t = sub r >>= \(b, r') -> go (f a b) r'
        go a r = Right (a, r)

-- Precedence, loosest first:  |   ||   xor   &&   ~   primary
pPar, pOr, pXor, pAnd, pUn, pPrim :: P SProc
pPar = chain (== TSym "|") SPar pOr
pOr = chain (== TSym "||") (SBin BOr) pXor
pXor = chain (== TId "xor") (SBin BXor) pAnd
pAnd = chain (== TSym "&&") (SBin BAnd) pUn
pUn (TSym "~" : r) = pUn r >>= \(a, r') -> Right (SNot a, r')
pUn ts = pPrim ts

pPrim (TZero : r) = Right (SNil, r)
pPrim (TId "true" : r) = Right (SBool True, r)
pPrim (TId "false" : r) = Right (SBool False, r)
pPrim (TSym "*" : r) = pName r >>= \(n, r') -> Right (SDrop n, r')
pPrim (TId "for" : r0) = do
  r1 <- expect "(" r0
  (p, r2) <- pPtrn r1
  (pers, r3) <- case r2 of
    (TSym "<-" : r) -> Right (False, r)
    (TSym "<=" : r) -> Right (True, r)
    _ -> Left ("expected <- or <= at " ++ ctx r2)
  (x, r4) <- pName r3
  r5 <- expect ")" r4
  (b, r6) <- pUn r5
  Right (SFor pers p x b, r6)
pPrim (TSym "(" : r) = pPar r >>= \(a, r') -> expect ")" r' >>= \r'' -> Right (a, r'')
pPrim (TSym "{" : r) = pPar r >>= \(a, r') -> expect "}" r' >>= \r'' -> Right (a, r'')
pPrim ts@(t : _) | nameStart t = do
  (n, r) <- pName ts
  r1 <- expect "!" r
  r2 <- expect "(" r1
  (q, r3) <- pPar r2
  r4 <- expect ")" r3
  Right (SSend n q, r4)
pPrim ts = Left ("unexpected " ++ ctx ts)

nameStart :: Tok -> Bool
nameStart (TSym "@") = True
nameStart (TId w) = w `notElem` keywords
nameStart _ = False

pName :: P SName
pName (TSym "@" : r) = pPrim r >>= \(p, r') -> Right (SQuote p, r')
pName (TId w : r) | w `notElem` keywords = Right (SId w, r)
pName ts = Left ("expected a name at " ++ ctx ts)

pPtrn :: P SPtrn
pPtrn (TSym "@" : r) = pDPrim r >>= \(d, r') -> Right (PtQuote d, r')
pPtrn (TId w : r) | w `notElem` keywords = Right (PtVar w, r)
pPtrn ts = Left ("expected a pattern at " ++ ctx ts)

pDP, pDXor, pDAnd, pDUn, pDPrim :: P SDP
pDP = chain (== TSym "||") (DBin BOr) pDXor
pDXor = chain (== TId "xor") (DBin BXor) pDAnd
pDAnd = chain (== TSym "&&") (DBin BAnd) pDUn
pDUn (TSym "~" : r) = pDUn r >>= \(a, r') -> Right (DNot a, r')
pDUn ts = pDPrim ts

pDPrim (TZero : r) = Right (DNil, r)
pDPrim (TId "true" : r) = Right (DBool True, r)
pDPrim (TId "false" : r) = Right (DBool False, r)
pDPrim (TId "for" : _) =
  Left "receive patterns (matching under a binder) are rejected: open question in the spec, Section 10"
pDPrim (TSym "(" : r) = pDP r >>= \(a, r') -> expect ")" r' >>= \r'' -> Right (a, r'')
pDPrim ts@(TSym "@" : _) = pPtrn ts >>= uncurry dsend
pDPrim (TId w : r@(TSym "!" : _)) | w `notElem` keywords = dsend (PtVar w) r
pDPrim (TId w : r) | w `notElem` keywords = Right (DVar w, r)
pDPrim ts = Left ("expected a deep pattern at " ++ ctx ts)

dsend :: SPtrn -> P SDP
dsend p r = do
  r1 <- expect "!" r
  r2 <- expect "(" r1
  (d, r3) <- pDP r2
  r4 <- expect ")" r3
  Right (DSend p d, r4)

parseProgram :: String -> Either String SProc
parseProgram s = do
  ts <- lexer s
  (p, r) <- pPar ts
  if null r then Right p else Left ("trailing input at " ++ ctx r)
