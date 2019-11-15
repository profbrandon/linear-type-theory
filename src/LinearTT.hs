--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/14/19                --
--------------------------------------------

module Main
  (
    main

  ) where


-- Foriegn Imports
import Data.List(stripPrefix, isSuffixOf)
import Data.Char(isSpace)
import System.IO(BufferMode(..), stdin, stdout, hGetLine, hPutStr, hSetBuffering)
import System.Environment(getArgs)
import System.Directory(doesFileExist)

-- Domestic Imports
import Typing(typeof, typeof0, typeofT)
import Eval(eval, subAll)
import Parser(parse, parseJ)

import Contexts(Context(..), push)
import Primitives(Type(..), Term(..), Judgement(..))

import Interactive(State(..), LineType(..))
import Commands(commands)


-- | The main function is the program entry point.
main :: IO ()
main = do 
  putStrLn "~~~~~ Linear Type Theory Interpreter v2.0 ~~~~~"
  putStrLn "             For help,  type :help             "
  putStrLn ""
  hSetBuffering stdout NoBuffering

  args <- getArgs
  if null args then
    loop ([], [], "")
  else do
    putStrLn "~ Loading Files ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
    (js, loaded) <- getFiles (reverse args)
    putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
    defs <- run True [] js
    putStrLn ""
    loop (loaded, defs, "")

-- | The getFiles function takes a list of filenames and repeatedly
-- checks to see if they are the right file type, they exist, and 
-- then proceeds to parse them. The output is the list of success-
-- fully parsed judgements and a list of the successfully loaded
-- files. 
getFiles :: [String] -> IO ([Judgement], [String])
getFiles [] = return ([], [])
getFiles (f:fs) = do
  exists <- doesFileExist f
  if ".ltt" `isSuffixOf` f then
    if exists then do
      str <- readFile f
      case parseJ str of
        Left  _  -> do putStrLn $ "Import file '" ++ f ++ "' could not be loaded."; getFiles fs
        Right js -> do 
          putStrLn $ "File '" ++ f ++ "' loaded."
          (back, loaded) <- getFiles fs
          return (js ++ back, f:loaded)
    else do
      putStrLn $ "The file '" ++ f ++ "' does not exist."
      getFiles fs
  else do
    putStrLn $ "Could not load '" ++ f ++ "' as it should have the .ltt file extension."
    getFiles fs

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
    Command c a -> do 
      state' <- handleCommand state c a
      loop state'
    Input s     ->
      let trim  = reverse . (dropWhile isSpace) . reverse . (dropWhile isSpace)
          s'    = trim s
          input = if last s' == ';' then s' else s' ++ ";"
      in case parseJ input of
        Left i -> case parse $ filter (/= ';') input of
          Left i -> do 
            putStrLn $ "Error: Parse failed at " ++ show i
            loop state
          Right e -> do 
            defs' <- run False defs [Normal e]
            loop (filenames, defs', prelude)
        Right js -> do 
          defs' <- run False defs js
          loop (filenames, defs', prelude)

-- | The getLineType gets the data representing what type of line it has recieved
-- from the input stream.
getLineType :: String -> LineType
getLineType (':':input) =
  case ws of
    [] -> Null
    _  -> let cmd  = head ws
              args = tail ws
          in case cmd of
            "exit" -> Exit
            _      -> Command cmd args
  where ws = words input

getLineType s = Input s

-- | The handleCommand function executes the given commands and returns (IO) False
-- if the exit command was called and (IO) True otherwise. For unrecognized
-- commands, the function reports this fact to the user.
handleCommand :: State -> String -> [String] -> IO State
handleCommand state cmd args =
  case cmd `lookup` commands of
    Nothing -> do putStrLn $ "Unrecognized command '" ++ cmd ++ "'"; return state
    Just f  -> f state args

-- | The run command takes as input a list of definitions, a list of judge-
-- ments, and computes the action associated with a judgement. For 'Define'
-- judgements, the function adds the definition to its list and continues 
-- with the rest of the judgements. For 'Typeof' judgements, the function
-- calculates the type of the corresponding term. For 'Normal' judgements,
-- the function normalizes the corresponding term and hence evaluates it.
run :: Bool -> [(String, Term)] -> [Judgement] -> IO [(String, Term)]
run _ defs [] = return defs

run bool defs ((Define s (Left e)):js) = do
  let e' = subAll e defs
  case typeof0 [] e' of
    Left err -> do putStrLn $ "Error: " ++ err; run bool defs js
    Right  _ -> run bool ((s,e'):defs) js

run bool defs (j@(Typeof (Left e)):js) = do
  if bool then putStrLn $ "> " ++ show j else return ()
  case typeof0 [] (subAll e defs) of
    Left err -> putStrLn $ "Error: " ++ err
    Right  t -> putStrLn $ "  : " ++ show t
  run bool defs js

run bool defs (j@(Typeof (Right t)):js) = do
  if bool then putStrLn $ "> " ++ show j else return ()
  case typeofT t of
    Left err -> putStrLn $ "Error: " ++ err
    Right t' -> putStrLn $ "  : " ++ show t'
  run bool defs js

run bool defs (j@(Normal e):js) = do
  if bool then putStrLn $ "> " ++ show j else return ()
  let e' = subAll e defs
  case typeof0 [] e' of
    Left err -> putStrLn $ "Error: " ++ err
    Right _  -> putStrLn $ "==> " ++ show (eval e')
  run bool defs js
