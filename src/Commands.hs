--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/14/19                --
--------------------------------------------

module Commands
  (
    Command(..)
  , commands

  ) where


-- Foriegn Imports
import System.Process(callCommand)

-- Domestic Imports
import Interactive(State(..))


-- The command datum represents the type signature of a command
type Command = State -> [String] -> IO State


-- This list maps strings to commands
commands :: [(String, Command)]
commands = 
  [
    ("imports", cmd_imports),
    ("names", cmd_names),
    ("unbind", cmd_unbind),
    ("system", cmd_system),
    ("help", cmd_help)
  ]

-- | The cmd_imports command represents the interactive environment command
-- 'imports' which displays which files are presently in the import list.
cmd_imports :: Command
cmd_imports state@(files,_,_) _ = do
  case reverse files of 
    []     -> putStrLn "No imported files" 
    (f:fs) -> putStrLn $ "Imports: " ++ foldl (\f1 f2 -> "'" ++ f1 ++ "', '" ++ f2 ++ "'") ("'" ++ f ++ "'") fs
  return state

-- | The cmd_names command represents the interactive environment command
-- 'names' which displays the bound names.
cmd_names :: Command 
cmd_names state@(_,defs,_) _ = do
  case reverse defs of
    []         -> putStrLn "No names have been defined"
    ((s,_):ds) -> putStrLn $ "Bound names: " ++ foldl (\s1 (s2,_) -> s1 ++ ", " ++ s2) s ds
  return state

-- | The cmd_unbind command represents the interactive environment command
-- 'unbind' which unbinds all of the names that are bound in the present 
-- environment.
cmd_unbind :: Command
cmd_unbind state [] = do putStrLn "Command 'unbind' expects a name argument"; return state
cmd_unbind (fs,defs,pre) names = do
  return (fs, removeAll names defs, pre)
  where 
    remove name [] = []
    remove name ((s,e):ps) = if name == s then remove name ps else (s,e):remove name ps
    removeAll [] ls = ls
    removeAll (n:ns) ls = removeAll ns (remove n ls)

-- | The cmd_system command represents calling the operating system with a
-- specific command.
cmd_system :: Command
cmd_system state args = do callCommand (unwords args); return state

-- | The cmd_help command represents the interactive environment command
-- 'help' which summons the help menu.
cmd_help :: Command
cmd_help state _ = do putStrLn helpMenu; return state

-- | The helpMenu is exactly that.
helpMenu :: String
helpMenu =
  "\n\
   \Help Menu Syntax\n\n\

    \\t[name]                          An optional name\n\
    \\t{name}                          A name that occurs zero or more times\n\
    \\ta | b                           Either a or b must occur (not both)\n\n\n\
   

   \Terminal\n\n\

    \\tLinearTT {files}\n\n\n\


   \Commands\n\n\

    \\t:help                           Displays this help menu\n\n\

    \\t:exit                           Exits the interactive environment\n\n\

    \\t:system cmd                     Calls the system with the provided command\n\n\

    \\t:names                          Shows all of the names declared previously\n\
    \\t                                by definition judgements\n\n\

    \\t:unbind name {names}            Unbinds the names from their definitions\n\
    \\t                                (if they have one)\n\n\

    \\t:imports                        Displays the names of all imported files\n\n\n\


   \Judgements\n\n\

    \\tDefine name := term [;]         Binds the name to the term\n\n\

    \\tTypeof term [;]                 Computes the type of the term and displays\n\
    \\t                                it to the user\n\n\

    \\tNormal term [;]                 Computes the normal form of the term and\n\
    \\t                                displays it to the user\n\n\n\


   \Terms\n\n\
   
    \\tlowercase {alpha | numeric}     Variables\n\n\

    \\t*                               The 'unit' term\n\n\

    \\t( term )                        Term grouping via parenthesis\n\n\

    \\tterm term                       Term application\n\n\

    \\tterm @ term                     Pair creation\n\n\

    \\trecI ( Type , term , term )     Unit recursion. The type given should be\n\
    \\t                                the type of the first term. The type of\n\
    \\t                                the second term should be 'I'.\n\n\

    \\trec@ ( Type , term , term )     Pair recursion. The type given should be\n\
    \\t                                the second conclusion of the first term.\n\
    \\t                                To put this more concretely, if the first\n\
    \\t                                term is '\\ a b : I. a @ b' then the type\n\
    \\t                                should be 'I @ I'. The first term is a\n\
    \\t                                lambda expression from the terms of the\n\
    \\t                                given product to the result. The second\n\
    \\t                                term is the product.\n\n\

    \\t\\ var {vars} : Type             Lambda abstraction. A lambda allows the\n\
    \\t {, var {vars} : Type}          creation of variables in its body. Here,\n\
    \\t               . term           we allow variables of the same type to be\n\
    \\t                                collected (delimited by spaces) and var-\n\
    \\t                                iables of different types to be separated\n\
    \\t                                via commas. The introduced variables are\n\
    \\t                                added to the context of the body and are\n\
    \\t                                hence usable there.\n\n\n\


   \Types\n\n\

    \\tI                               The 'unit' type\n\n\

    \\t( Type )                        Type grouping via parenthesis\n\n\

    \\tType -+ Type                    Arrow types (Implication), created via\n\
    \\t                                lambdas.\n\n\

    \\tType @ Type                     Pair types (Conjunction), created via the\n\
    \\t                                pairing operator @.\n\n"