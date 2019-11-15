--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/13/19                --
--------------------------------------------

module Primitives
  ( 
    Type(..)
  , Term(..)
  , Judgement(..)
  
  ) where


-- | The Type datum is a representation of the types of the linear lambda
-- calculus.
data Type =
    Unit
  | Arrow Type Type
  | Prod  Type Type
--  | Bang  Type
  | Univ  Int
  deriving (Eq)

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
--  | Promote  [Term] [String] Term
--  | Derelict Term
--  | Copy     Term String String Term
--  | Discard  Term Term
  deriving (Eq)

-- | The Judgement datum gives representations for certain interpreter
-- actions.
data Judgement =
    Define String (Either Term Type)
  | Typeof (Either Term Type)
  | Normal Term