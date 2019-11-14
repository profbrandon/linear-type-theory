--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/12/19                --
--------------------------------------------

module Main
  (
    main

  ) where




-- Foriegn Imports
import Data.List (stripPrefix)

-- Domestic Imports
import Typing (typeof)
import Eval (eval)
import Parser (parse)
import Primitives (Type(..), Term(..))




main :: IO ()
main = do
  putStrLn "Linear Type Theory Interactive"
  putStrLn "------------------------------"
  loop
  where
    loop = do
      s <- getLine
      case s of
        "exit" -> return ()
        ""     -> loop
        _      -> do
          case stripPrefix "typeof " s of
            Nothing -> 
              case compute s of 
                Left message -> putStrLn $ "Error: " ++ message
                Right (e, _) -> putStrLn $ "==> " ++ show e
            Just s' ->
              case compute s' of
                Left message -> putStrLn $ "Error: " ++ message
                Right (_, t) -> putStrLn $ "  : " ++ show t
          loop

compute :: String -> Either String (Term, Type)
compute s =
  case parse s of
    Left i -> Left $ "Parsing failed at " ++ show i
    Right e ->
      case typeof e of
        Left  err -> Left err
        Right t   -> Right (e,t)