-- | Command-line driver: run a source program on the machine model under the
-- step-refinement checker.
module Main (main) where

import Data.Maybe (mapMaybe)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Rho.Checker
import Rho.Core
import Rho.Machine

usage :: String
usage = unlines
  [ "usage: rhoref run FILE [--seed N] [--steps N] [--egress a,b,...]"
  , "       rhoref norm FILE"
  , ""
  , "run   load FILE, step the machine model to quiescence (or N steps),"
  , "      checking every step against the reference semantics"
  , "norm  print the normal form and the symbol table" ]

opt :: String -> [String] -> Maybe String
opt k (a : v : r) | a == k = Just v
                  | otherwise = opt k (v : r)
opt _ _ = Nothing

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
  (a, []) -> [a]
  (a, _ : r) -> a : splitOn c r

die' :: String -> IO a
die' msg = hPutStrLn stderr msg >> exitFailure

main :: IO ()
main = getArgs >>= \args -> case args of
  ("norm" : file : _) -> do
    (p, syms) <- readFile file >>= either die' pure . compileSource
    putStrLn ("symbols: " ++ unwords syms)
    putStrLn (ppProc syms p)
  ("run" : file : rest) -> do
    (p, syms) <- readFile file >>= either die' pure . compileSource
    let seed = maybe 1 read (opt "--seed" rest)
        steps = maybe 1000 read (opt "--steps" rest)
        ports = maybe [] (splitOn ',') (opt "--egress" rest)
        eg = mapMaybe (symName syms) ports
    putStrLn ("program:  " ++ ppProc syms p)
    case runChecked defaultParams seed eg p steps of
      Left err -> die' ("CHECK FAILED\n" ++ err)
      Right rr -> do
        mapM_ (\(i, (s, r, row)) -> putStrLn ("step " ++ show i ++ ": send slot " ++ show s
                                              ++ ", receive slot " ++ show r ++ ", row " ++ show row))
              (zip [0 :: Int ..] (rrDecisions rr))
        mapM_ (putStrLn . ("egress:   " ++) . ppProc syms) (rrEgress rr)
        putStrLn ("final:    " ++ ppProc syms (last (rrStates rr)))
        putStrLn (case rrFault rr of
          Just f -> "halted on " ++ show f
          Nothing | rrQuiescent rr -> "quiescent after " ++ show (length (rrDecisions rr)) ++ " steps; every step checked"
                  | otherwise -> "step limit reached; every step checked")
  _ -> putStr usage
