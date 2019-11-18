--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/18/19                --
--------------------------------------------

module Parser
  ( 
    parse
  , parseJ
    
  ) where


-- Foriegn Imports
import Prelude hiding (either)
import Control.Applicative ((<|>))
import Text.ParserCombinators.ReadP

-- Domestic Imports
import Primitives (Type(..), Term(..), Judgement(..))


-- Parsers

parseJ :: String -> Either Int [Judgement]
parseJ s = 
  case readP_to_S judgements s of
    [] -> Left (-1)
    l -> let (e, s') = last l in
      if s' == "" then Right e else Left $ length s - length s'

parse :: String -> Either Int Term
parse s = 
  case readP_to_S a_term s of
    [] -> Left (-1)
    l  -> let (e, s') = last l in
      if s' == "" then Right e else Left $ length s - length s'

-- Helpers

lowercase :: ReadP Char
lowercase = satisfy (\c -> c >= 'a' && c <= 'z')

uppercase :: ReadP Char
uppercase = satisfy (\c -> c >= 'A' && c <= 'Z')

alpha :: ReadP Char
alpha = lowercase <|> uppercase

numeric :: ReadP Char
numeric = satisfy (\c -> c >= '0' && c <= '9')

nonzero :: ReadP Int
nonzero = do
  d <- satisfy (\c -> c >= '1' && c <= '9')
  ds <- many numeric
  return (read (d:ds) :: Int)

alnum :: ReadP Char
alnum = alpha <|> numeric

either :: ReadP a -> ReadP b -> ReadP (Either a b)
either q p = readS_to_P (
    \s -> case readP_to_S p s of
      [] -> map (\(x,y) -> (Left x, y)) $ readP_to_S q s
      ls -> map (\(x,y) -> (Right x, y)) ls
  )



-- Judgements

judgements :: ReadP [Judgement]
judgements = do 
  skipSpaces
  js <- sepBy (define <++ typeof <++ normal) skipSpaces
  skipSpaces
  return js

define :: ReadP Judgement
define = do
  string "Define"
  skipSpaces
  name <- (do c <- alpha; cs <- many alnum; return (c:cs))
  skipSpaces
  string ":="
  skipSpaces
  e <- either a_term a_type
  skipSpaces
  char ';'
  return (Define name e)

typeof :: ReadP Judgement
typeof = do
  string "Typeof"
  skipSpaces
  e <- either a_term a_type
  skipSpaces
  char ';'
  return (Typeof e)

normal :: ReadP Judgement
normal = do
  string "Normal"
  skipSpaces
  e <- a_term
  skipSpaces
  char ';'
  return (Normal e)


-- Variables 

term_var :: ReadP Term
term_var = do 
  c <- lowercase
  cs <- many (alnum)
  return (Var $ c:cs)

type_var :: ReadP Type
type_var = do 
  c <- uppercase
  cs <- many (alnum)
  return (TVar $ c:cs)


-- Unit and Star

unit :: ReadP Type
unit = do char 'I'; return Unit

star :: ReadP Term
star = do char '*'; return Star

-- Types

a_type :: ReadP Type
a_type = do
  t1 <- unit <++ universe <++ pi_type <++ type_var <++ a_type_paren
  (do t2 <- prod_back; return (Prod t1 t2)) 
    <|> (do t2 <- arrow_back; return (Pi "_" t1 t2))
    <|> return t1

a_type_paren :: ReadP Type
a_type_paren = do
  char '('
  skipSpaces
  t <- a_type
  skipSpaces
  char ')'
  return t

pi_type :: ReadP Type
pi_type = do
  string "forall"
  skipSpaces
  judges <- sepBy1 type_judges (do skipSpaces; char ','; skipSpaces)
  let js = foldl (++) [] judges
  skipSpaces
  char '.'
  skipSpaces
  t <- a_type
  return (convert js t)
  where
    convert [] t         = t
    convert ((s,t'):ls) t = Pi s t' (convert ls t)

arrow_back :: ReadP Type
arrow_back = do
  skipSpaces
  string "-+"
  skipSpaces
  t2 <- a_type
  return t2

prod_back :: ReadP Type
prod_back = do
  skipSpaces
  char '@'
  skipSpaces
  t2 <- a_type
  return t2

universe :: ReadP Type
universe = do
  char 'U'
  skipSpaces
  char '@'
  skipSpaces
  i <- nonzero
  return (Univ i)


-- Terms

a_term :: ReadP Term
a_term = do
  e1 <- single_term
  handle_back e1

single_term :: ReadP Term
single_term = star <++ lambda <++ (recI <|> recPair) <++ term_var <++ a_term_paren

a_term_paren :: ReadP Term
a_term_paren = do
  char '('
  skipSpaces
  e <- a_term
  skipSpaces 
  char ')'
  return e

handle_back :: Term -> ReadP Term
handle_back e1 = do
   e2 <- option e1 (do e2 <- pair_back; return (Pair e1 e2))
   e3 <- option e2 (do t <- appT_back; handle_back (AppT e2 t))
   option e3 (do e4 <- app_back; handle_back (App e3 e4))

app_back :: ReadP Term
app_back = do skipSpaces; single_term

appT_back :: ReadP Type
appT_back = do skipSpaces; a_type

pair_back :: ReadP Term
pair_back = do
  skipSpaces
  char '@'
  skipSpaces
  e1 <- single_term
  handle_back e1

type_judges :: ReadP [(String,Type)]
type_judges = do
  ss <- sepBy1 (do c <- alpha; cs <- many alnum; return (c:cs)) skipSpaces
  skipSpaces
  char ':'
  skipSpaces
  t <- a_type
  return (fmap (\s -> (s, t)) ss)

lambda :: ReadP Term
lambda = do
  char '\\'
  skipSpaces
  judgements <- sepBy1 type_judges (do skipSpaces; char ','; skipSpaces)
  let js = foldl (++) [] judgements
  skipSpaces
  char '.'
  skipSpaces
  e <- a_term
  return (convert js e)
  where
    convert [] e         = e
    convert ((s,t):ls) e = Lambda s t (convert ls e)

recA :: String -> (Type -> Term -> Term -> Term) -> ReadP Term
recA s f = do
  string s
  skipSpaces
  char '('
  skipSpaces
  t <- a_type
  skipSpaces
  char ','
  skipSpaces
  e1 <- a_term
  skipSpaces
  char ','
  skipSpaces
  e2 <- a_term
  skipSpaces
  char ')'
  return (f t e1 e2)

recI = recA "recI" RecI
recPair = recA "rec@" RecPair