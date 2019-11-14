--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/14/19                --
--------------------------------------------

module Eval
  ( 
    eval
  , subAll
  
  ) where


-- Domestic Imports
import Primitives(Term(..))

-- Foriegn Imports
import Data.List((\\), elem)


-- | The eval function performs reduction on the terms until a normal
-- form is reached.
eval :: Term -> Term
eval e = if e' == e then e else eval e' where e' = eval0 e

-- | The eval0 function is a helper function for eval that does one
-- step of evaluation at the root and simplifies the subterms. The top
-- half of the equations represent actual reduction, specifically,
-- beta-reduction, recursion computation for the unit, recursion comp-
-- utation for pairs, and eta-reduction. The lower half of the 
-- equations are merely propagating evaluation.
eval0 :: Term -> Term
eval0 (App (Lambda s _ e) e')          = sub e (s, e')
eval0 (RecI t e Star)                  = e
eval0 (RecPair t e (Pair a b))         = App (App e a) b
eval0 l@(Lambda s t (App e1 (Var s1))) = 
  if s1 == s then 
    if s `elem` getFreeVars e1 then l else e1
  else
    l 

eval0 (Var s)                  = Var s
eval0 Star                     = Star
eval0 (RecI t e1 e2)           = RecI t (eval0 e1) (eval0 e2)
eval0 (Pair e1 e2)             = Pair (eval0 e1) (eval0 e2)
eval0 (RecPair t e1 e2)        = RecPair t (eval0 e1) (eval0 e2)
eval0 (Lambda s t e)           = Lambda s t (eval0 e)
eval0 (App e1 e2)              = App (eval0 e1) (eval0 e2)

-- | The sub function performs variable substitution. It takes a term t,
-- a string x and a term u and performs t[u/x].
sub :: Term -> (String, Term) -> Term
sub (Var s)           (s', e)    = if s == s' then e else Var s
sub Star              _          = Star
sub (RecI t e1 e2)    p          = RecI t (sub e1 p) (sub e2 p)
sub (Pair e1 e2)      p          = Pair (sub e1 p) (sub e2 p)
sub (RecPair t e1 e2) p          = RecPair t (sub e1 p) (sub e2 p)
sub l@(Lambda s t e)  p@(s', e') = if s == s' then l else Lambda s t (sub e p)
sub (App e1 e2)       p          = App (sub e1 p) (sub e2 p)

-- | The subAll function takes a list of substitutions and applies all
-- of them.
subAll :: Term -> [(String, Term)] -> Term
subAll e ps = foldl sub e (reverse ps)

-- | The getFreeVars function takes a term and returns the list of free
-- variables in the term.
getFreeVars :: Term -> [String]
getFreeVars (Var s)           = [s]
getFreeVars Star              = []
getFreeVars (RecI t e1 e2)    = getFreeVars e1 ++ getFreeVars e2
getFreeVars (Pair e1 e2)      = getFreeVars e1 ++ getFreeVars e2
getFreeVars (RecPair t e1 e2) = getFreeVars e1 ++ getFreeVars e2
getFreeVars (Lambda s t e)    = getFreeVars e \\ [s]
getFreeVars (App e1 e2)       = getFreeVars e1 ++ getFreeVars e2