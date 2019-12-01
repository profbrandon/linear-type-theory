--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/30/19                --
--------------------------------------------

module Parser
  (
    parseTerm
  , parseJudge

  ) where


-- Foriegn Imports
import Text.Parsec ( parse, between, try, choice, parserZero )
import Text.Parsec.Error ( ParseError )
import Text.Parsec.String ( Parser )
import Text.Parsec.Expr ( Assoc(..) )
import Text.Parsec.Char ( oneOf, anyChar, char, string, digit, letter, satisfy, upper, lower, alphaNum )
import Text.Parsec.Combinator ( sepBy1, many1, manyTill, chainl1, chainr1, option )
import Control.Applicative ( (<$>), (<*>), (<*), (*>), (<|>), many, (<$) )
import Control.Monad ( void, ap, guard, join )
import Data.Char ( isLetter, isDigit )
import Data.List ( elem )

-- Domestic Imports
import Primitives ( Type(..), Term(..), Judgement(..) )


type OpTable a = [(String, Assoc, (a -> a -> a))]


-- Main Parsers

parseTerm :: String -> Either ParseError Term
parseTerm = parse a_term ""

parseJudge :: String -> Either ParseError [Judgement]
parseJudge = parse (whitespace *> many1 judgement) ""

-- Keywords

keywords :: [String]
keywords = [ "forall"
           , "I"
           , "inl"
           , "inr"
           , "rec"
           ]

-- Operators

type_op_table :: OpTable Type
type_op_table =
  [ ("@",  AssocLeft,  Prod)
  , ("+",  AssocLeft,  Sum)
  , ("-+", AssocRight, Pi "_")
  ]

term_op_table :: OpTable Term
term_op_table =
  [ ("@", AssocLeft, Pair)
  , ("",  AssocLeft, App)
  ]

convert_op_table :: Parser a -> OpTable a -> Parser a
convert_op_table p [] = p
convert_op_table p ((op, assoc, c):ops) = convert_op_table (parse_op p op assoc c) ops

parse_op :: Parser a -> String -> Assoc -> (a -> a -> a) -> Parser a
parse_op p op assoc c = p `f` (symbol op *> return c)
  where f = case assoc of AssocLeft  -> chainl1
                          AssocRight -> chainr1
                          AssocNone  -> \p q -> (\a c b -> c a b) <$> p <*> q <*> p

-- Basic Helper Parsers

var_char :: Parser Char
var_char = alphaNum <|> oneOf "_\'"

identifier :: Parser String
identifier = except keywords $ lexeme $ (:) <$> alpha <*> many var_char where alpha = lower <|> upper

nonzero :: Parser Int
nonzero = read <$> ((:) <$> (oneOf "123456789") <*> many digit)

simpleWhitespace :: Parser ()
simpleWhitespace = void $ many1 $ oneOf " \n\t"

whitespace :: Parser ()
whitespace = void $ many (simpleWhitespace <|> comment)

whitespace1 :: Parser ()
whitespace1 = void $ many1 (simpleWhitespace <|> comment)

comment :: Parser ()
comment = void $ char '#' <* manyTill anyChar (char '#')

-- Basic Combinators

parse_either :: Parser a -> Parser b -> Parser (Either a b)
parse_either p q = (Left <$> try p) <|> (Right <$> q)

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

symbol :: String -> Parser ()
symbol []  = return ()
symbol s   = void $ lexeme $ string s

paren :: Parser a -> Parser a
paren p = between (symbol "(") (symbol ")") p 

except :: Eq a => [a] -> Parser a -> Parser a
except ls p = do {l <- p; if l `elem` ls then parserZero else return l}

-- Variables

type_var :: Parser Type
type_var = TVar <$> (except keywords $ lexeme $ (:) <$> upper <*> many var_char)

term_var :: Parser Term
term_var = Var <$> (except keywords $ lexeme $ (:) <$> lower <*> many var_char)

type_ann :: Parser [(String, Type)]
type_ann = fillType <$> (many1 identifier <* symbol ":") <*> a_type
  where fillType ss t = fmap (\s -> (s,t)) ss

-- Constants (For terms and types)

unit_type :: Parser Type
unit_type = return Unit <* symbol "I"

univ_type :: Parser Type
univ_type = symbol "U" *> symbol "@" *> (Univ <$> nonzero)

unit_term :: Parser Term
unit_term = return Star <* symbol "*"

-- Types

a_type :: Parser Type
a_type = op_type <|> pi_type <|> basic_type
  where op_type = convert_op_table basic_type type_op_table

basic_type :: Parser Type
basic_type = unit_type <|> univ_type <|> type_var <|> paren a_type 

pi_type :: Parser Type
pi_type = mapPi <$> (symbol "forall" *> (join <$> sepBy1 type_ann (symbol ",")) <* symbol ".") <*> a_type
  where mapPi as u = foldr (\(s,t) back -> Pi s t back) u as

-- Terms

a_term :: Parser Term
a_term = try op_term <|> lambda_term 
  where
    op_term = convert_op_table appT_term term_op_table

basic_term :: Parser Term
basic_term = 
      unit_term 
  <|> try (rec_term "I" RecI) <|> try (rec_term "@" RecPair) <|> try rec_sum 
  <|> try (inj_term "inl" Inl) <|> try (inj_term "inr" Inr)
  <|> term_var <|> paren a_term

lambda_term :: Parser Term
lambda_term = mapLambda <$> (symbol "\\" *> (join <$> sepBy1 type_ann (symbol ",")) <* symbol ".") <*> a_term
  where mapLambda as u = foldr (\(s,t) back -> Lambda s t back) u as

appT_term :: Parser Term
appT_term = do {e1 <- basic_term; back e1}
  where back e     = do {e' <- appT_one e; if e /= e' then back e' else return e}
        appT_one e = option e $ AppT e <$> try basic_type

rec_term :: String -> (Type -> Term -> Term -> Term) -> Parser Term
rec_term s c = symbol ("rec" ++ s) *> paren (c <$> a_type <*> (symbol "," *> a_term) <*> (symbol "," *> a_term))

rec_sum :: Parser Term
rec_sum = symbol "rec+" *> paren (RecSum <$> a_type <*> term_field <*> term_field <*> term_field)
  where term_field = symbol "," *> a_term

inj_term :: String -> (Type -> Term -> Term) -> Parser Term
inj_term s c = symbol s *> (c <$> basic_type <*> basic_term)

-- Judgements

judgement :: Parser Judgement
judgement = try define <|> try typeof <|> normal

define :: Parser Judgement
define = Define <$> (symbol "Define" *> identifier <* symbol ":=") 
  <*> (parse_either a_term a_type <* symbol ";")

typeof :: Parser Judgement
typeof = Typeof <$> (symbol "Typeof" *> parse_either a_term a_type <* symbol ";")

normal :: Parser Judgement
normal = Normal <$> (symbol "Normal" *> a_term <* symbol ";")