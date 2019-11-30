--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/23/19                --
--------------------------------------------

module Main
  (
    main

  ) where


-- Foriegn Imports
import Data.List ( stripPrefix, isSuffixOf )
import Data.Char ( isSpace )
import System.IO ( BufferMode(..), stdin, stdout, hGetLine, hPutStr, hSetBuffering )
import System.Environment ( getArgs )
import System.Directory ( doesFileExist )
import Control.Monad ( mapM, join )
import Control.Applicative ( (<$>), (<|>), (<*>), (<*), (*>) )

-- Domestic Imports
import Typing ( typeof, typeof0, typeofT, typeofT0 )
import Eval ( eval, subAll, subAllT )
import Parser ( parseTerm, parseJudge )
import Contexts ( Context(..), push )
import Primitives ( Type(..), Term(..), Judgement(..), Definition(..) )
import Interactive ( State(..), LineType(..) )
import Commands ( commands )


-- | The main function is the program entry point.
main :: IO ()
main = do 
  putStrLn "~~~~~ Linear Type Theory Interpreter v2.1 ~~~~~"
  putStrLn "             For help,  type :help             "
  putStrLn ""
  hSetBuffering stdout NoBuffering

  args <- getArgs
  if null args then
    loop ([], [], "")
  else do
    putStrLn "~ Loading Files ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
    (js, loaded, err) <- getFiles (reverse args) []
    putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
    mapM putStrLn err
    defs <- run True [] js <* putStrLn ""
    loop (loaded, defs, "")

-- | The getFiles function takes a list of filenames and repeatedly
-- checks to see if they are the right file type, they exist, and 
-- then proceeds to parse them. The output is the list of success-
-- fully parsed judgements and a list of the successfully loaded
-- files. 
getFiles :: [String] -> [String] -> IO ([Judgement], [String], [String])
getFiles []     err = return ([], [], err)
getFiles (f:fs) err = do
  exists <- doesFileExist f
  if ".ltt" `isSuffixOf` f then
    if exists then do
      str <- readFile f
      case parseJudge str of
        Left  s  -> do putStrLn $ "Import file '" ++ f ++ "' could not be loaded."; getFiles fs ((show s):err)
        Right js -> do 
          putStrLn $ "File '" ++ f ++ "' loaded."
          (back, loaded, err') <- getFiles fs err
          return (js ++ back, f:loaded, err')
    else do
      putStrLn ("The file '" ++ f ++ "' does not exist.") *> getFiles fs err
  else do
    putStrLn ("Could not load '" ++ f ++ "' as it should have the .ltt file extension.") *> getFiles fs err

-- | The loop function is the main program loop that repeatedly handles
-- commands and judgements. It is constantly repassing state to itself
-- in order to accomodate any changes in state.
loop :: State -> IO ()
loop state@(filenames, defs, prelude) = do
  hPutStr stdout "Linear Type Theory> "
  s <- hGetLine stdin

  case getLineType s of
    Exit        -> return ()
    Null        -> loop state
    Command c a -> join $ loop <$> handleCommand state c a
    Input s     ->
      let trim  = reverse . (dropWhile isSpace) . reverse . (dropWhile isSpace)
          s'    = trim s
          input = if last s' == ';' then s' else s' ++ ";"
      in case parseJudge input of
        Left s -> case parseTerm $ filter (/= ';') input of
                    Left s' -> putStrLn ("Error: " ++ show s) *> putStrLn ("Error: " ++ show s') *> loop state
                    Right e -> join $ (\d -> loop (filenames, d, prelude)) <$> run False defs [Normal e]
        Right js -> join $ (\d -> loop (filenames, d, prelude)) <$> run False defs js

-- | The getLineType gets the data representing what type of line it has recieved
-- from the input stream.
getLineType :: String -> LineType
getLineType "" = Null
getLineType (':':input) =
  case ws of
    [] -> Null
    _  -> let cmd  = head ws
              args = tail ws
          in case cmd of
            "exit" -> Exit
            _      -> Command cmd args
  where ws = words input

getLineType s
  | and (map isSpace s) = Null
  | otherwise           = Input s

-- | The handleCommand function executes the given commands and returns (IO) False
-- if the exit command was called and (IO) True otherwise. For unrecognized
-- commands, the function reports this fact to the user.
handleCommand :: State -> String -> [String] -> IO State
handleCommand state cmd args =
  case cmd `lookup` commands of
    Nothing -> putStrLn ("Unrecognized command '" ++ cmd ++ "'") *> return state
    Just f  -> f state args

-- | The run command takes as input a list of definitions, a list of judge-
-- ments, and computes the action associated with a judgement. For 'Define'
-- judgements, the function adds the definition to its list and continues 
-- with the rest of the judgements. For 'Typeof' judgements, the function
-- calculates the type of the corresponding term. For 'Normal' judgements,
-- the function normalizes the corresponding term and hence evaluates it.
run :: Bool -> [Definition] -> [Judgement] -> IO [Definition]
run _ defs [] = return defs

run bool defs ((Define s (Left e)):js) = do
  let e' = subAll e defs
  case typeof e' of
    Left err -> putStrLn ("Error: " ++ err) *> run bool defs js
    Right  _ -> run bool ((s, Left e'):defs) js

run bool defs ((Define s (Right t)):js) = do
  case typeofT t of
    Left err -> putStrLn ("Error: " ++ err) *> run bool defs js
    Right  _ -> run bool ((s, Right t):defs) js

run bool defs (j@(Typeof (Left e)):js) = do
  if bool then putStrLn $ "> " ++ show j else return ()
  case typeof (subAll e defs) of
    Left err -> putStrLn $ "Error: " ++ err
    Right  t -> putStrLn $ "  : " ++ show t
  run bool defs js

run bool defs (j@(Typeof (Right t)):js) = do
  if bool then putStrLn $ "> " ++ show j else return ()
  let t' = subAllT t defs
  case typeofT t' of
    Left err  -> putStrLn $ "Error: " ++ err
    Right t'' -> putStrLn $ "  : " ++ show t''
  run bool defs js

run bool defs (j@(Normal e):js) = do
  if bool then putStrLn $ "> " ++ show j else return ()
  let e' = subAll e defs
  case typeof e' of
    Left err -> putStrLn $ "Error: " ++ err
    Right _  -> putStrLn $ "==> " ++ show (eval e')
  run bool defs js
