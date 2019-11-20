--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/19/19                --
--------------------------------------------

module Eval
  ( 
    eval

  , subAll, subAllT
  
  ) where


-- Domestic Imports
import Primitives ( Term(..), Type(..), Definition(..) )
import Contexts ( getFreeVars )

-- Foriegn Imports
import Data.List ( elem )


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
eval0 (App (Lambda s _ e) e')          = sub e (s, Left e')
eval0 (AppT (Lambda s _ e) t)          = sub e (s, Right t)
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
eval0 (App  e1 e2)             = App (eval0 e1) (eval0 e2)
eval0 (AppT e  t)              = AppT (eval0 e) t

-- | The sub function performs variable substitution. It takes a term t,
-- and a definition and performs t[u/x].
sub :: Term -> Definition -> Term
sub (Var s)           (s', Left  e)  = if s == s' then e else Var s
sub (Var s)           (_,  Right _)  = Var s
sub Star              _              = Star
sub (RecI t e1 e2)    p@(_, Left  _) = RecI t (sub e1 p) (sub e2 p)
sub (RecI t e1 e2)    p@(_, Right _) = RecI (subT t p) (sub e1 p) (sub e2 p)

sub (Pair e1 e2)      p              = Pair (sub e1 p) (sub e2 p)

sub (RecPair t e1 e2) p@(_, Left  _) = RecPair t (sub e1 p) (sub e2 p)
sub (RecPair t e1 e2) p@(_, Right _) = RecPair (subT t p) (sub e1 p) (sub e2 p)

sub l@(Lambda s t e)  p@(s', _)      = if s == s' then l else Lambda s (subT t p) (sub e p)
sub (App  e1 e2)      p              = App (sub e1 p) (sub e2 p)
sub (AppT e  t)       p              = AppT (sub e p) (subT t p)

-- | The subT function performs variable substitution in a type. It takes
-- a type t and a definition and performs the corresponding substitution.
subT :: Type -> Definition -> Type
subT (TVar s)       (_ , Left  _)   = TVar s
subT (TVar s)       (s', Right t)   = if s == s' then t else TVar s
subT u@(Univ _)     _               = u
subT Unit           _               = Unit
subT (Pi s t1 t2)   p@(_ , Left  _) = Pi s (subT t1 p) (subT t2 p)
subT l@(Pi s t1 t2) p@(s', Right t) = if s == s' then l else Pi s (subT t1 p) (subT t2 p)
subT (Prod t1 t2)   p               = Prod (subT t1 p) (subT t2 p)

-- | The subAll function takes a term and a list of definitions and sub-
-- stitutes all strings bound to the definition.
subAll :: Term -> [Definition] -> Term
subAll e ps = foldl sub e (reverse ps)

-- | The subAllT function takes a type and a list of definitions and sub-
-- stitutes all strings bound to the defintion.
subAllT :: Type -> [Definition] -> Type
subAllT t ps = foldl subT t (reverse ps)