--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/18/19                --
--------------------------------------------

module Primitives
  ( 
    Type(..)
  , Term(..)
  , Judgement(..)
  , Definition(..)
  
  ) where


-- | The Type datum is a representation of the types of the linear lambda
-- calculus.
data Type =
    TVar String
  | Unit
  | Pi   String Type Type
  | Prod Type Type
  | Univ Int
  deriving Eq

-- | The Term datum is a representation of the terms of the linear lambda
-- calculus.
data Term =
    Var String
  | Star
  | RecI     Type Term Term
  | Pair     Term Term
  | RecPair  Type Term Term
  | Lambda   String Type Term
  | App      Term Term
  | AppT     Term Type
  deriving Eq

-- | The Judgement datum gives representations for certain interpreter
-- actions.
data Judgement =
    Define String (Either Term Type)
  | Typeof (Either Term Type)
  | Normal Term
  deriving Eq

-- | The Definition datum is a representation of the outcome of a define
-- judgement, i.e., binding a name to a value (whether it is a term or a
-- type).
type Definition = (String, Either Term Type)