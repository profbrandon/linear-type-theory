--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/23/19                --
--------------------------------------------

module Equiv
  (
    arrowEquiv

  , alphaEquiv, alphaEquivT

  , permuteEquiv

  ) where


-- Foreign Imports
import Data.List ( union, lookup, elem )

-- Domestic Imports
import Primitives ( Term(..), Type(..) )
import Contexts ( Context, getFreeVarsT )


-- | The arrowEquiv function tests if two Pi types are equivalent. This is
-- needed since, for e.g, I -+ I is technically Pi s I I and hence depends
-- on the name of the string s. (Even though it does not determine any
-- part of the final type)
arrowEquiv :: Type -> Type -> Bool
arrowEquiv p1@(Pi s t1 t2) p2@(Pi s' t1' t2') 
  | not (s `elem` (getFreeVarsT t2)) && not (s' `elem` (getFreeVarsT t2')) = t1 `arrowEquiv` t1' && t2 `arrowEquiv` t2'
  | otherwise = p1 == p2
arrowEquiv (TVar s)     (TVar s')      = s == s'
arrowEquiv (Prod t1 t2) (Prod t1' t2') = (arrowEquiv t1 t1') && (arrowEquiv t2 t2')
arrowEquiv (Univ i)     (Univ j)       = i == j
arrowEquiv t            t'             = t == t'

-- | The alphaEquiv function determines if two terms are alpha-equivalent
alphaEquiv :: Term -> Term -> Bool
alphaEquiv e e' = snd $ alphaEquiv0 [] e e'

-- | The alphaEquiv0 function is the helper function for alphaEquiv. It 
-- keeps track of the matched names.
alphaEquiv0 :: [(String, String)] -> Term -> Term -> ([(String, String)], Bool)
alphaEquiv0 b        Star    Star     = (b, True)
alphaEquiv0 bindings (Var s) (Var s')
  | (s, s') `elem` bindings = (bindings, True)
  | otherwise = case s `lookup` bindings of
                  Nothing -> back
                  Just ss
                    | ss == s'  -> (bindings, True)
                    | otherwise -> back
  where back = case s' `lookup` bindings of
                Nothing  -> (bindings, False)
                Just ss'
                  | ss' == s  -> (bindings, True) 
                  | otherwise -> (bindings, False)

alphaEquiv0 bindings (RecI t e1 e2) (RecI t' e1' e2') = (b0 `union` b1 `union` b2, a0 && a1 && a2)
  where (b0, a0) = alphaEquivT0 bindings t t'
        (b1, a1) = alphaEquiv0 bindings e1 e1'
        (b2, a2) = alphaEquiv0 bindings e2 e2'

alphaEquiv0 bindings (Pair e1 e2) (Pair e1' e2') = (b1 `union` b2, a1 && a2)
  where (b1, a1) = alphaEquiv0 bindings e1 e1'
        (b2, a2) = alphaEquiv0 bindings e2 e2'

alphaEquiv0 bindings (RecPair t e1 e2) (RecPair t' e1' e2') = (b0 `union` b1 `union` b2, a0 && a1 && a2)
  where (b0, a0) = alphaEquivT0 bindings t t'
        (b1, a1) = alphaEquiv0 bindings e1 e1'
        (b2, a2) = alphaEquiv0 bindings e2 e2'

alphaEquiv0 bindings (Lambda s t e) (Lambda s' t' e') = (b0 `union` b1, a0 && a1)
  where bindings' = (s, s'):bindings
        (b0, a0)  = alphaEquivT0 bindings t t'
        (b1, a1)  = alphaEquiv0 bindings' e e'

alphaEquiv0 bindings (App e1 e2) (App e1' e2') = (b1 `union` b2, a1 && a2)
  where (b1, a1) = alphaEquiv0 bindings e1 e1'
        (b2, a2) = alphaEquiv0 bindings e2 e2'

alphaEquiv0 bindings (AppT e t) (AppT e' t') = (b0 `union` b1, a0 && a1)
  where (b0, a0) = alphaEquivT0 bindings t t'
        (b1, a1) = alphaEquiv0 bindings e e'

alphaEquiv0 b _ _ = (b, False)

-- | The alphaEquivT function determines if two types are alpha-equivalent.
alphaEquivT :: Type -> Type -> Bool
alphaEquivT t t' = snd $ alphaEquivT0 [] t t'

-- | The alphaEquivT0 function is the helper function for alphaEquivT
alphaEquivT0 :: [(String, String)] -> Type -> Type -> ([(String, String)], Bool)
alphaEquivT0 bindings Unit         Unit            = (bindings, True)
alphaEquivT0 bindings (Univ i)     (Univ j)        = (bindings, i == j)
alphaEquivT0 bindings (TVar s)     (TVar s')       = alphaEquiv0 bindings (Var s) (Var s')
alphaEquivT0 bindings (Pi s t1 t2) (Pi s' t1' t2') = (b1 `union` b2, a1 && a2)
  where bindings' = (s, s'):bindings
        (b1, a1)  = alphaEquivT0 bindings t1 t1'
        (b2, a2)  = alphaEquivT0 bindings' t2 t2'

alphaEquivT0 bindings (Prod t1 t2) (Prod t1' t2')  = (b1 `union` b2, a1 && a2)
  where (b1, a1) = alphaEquivT0 bindings t1 t1'
        (b2, a2) = alphaEquivT0 bindings t2 t2'

alphaEquivT0 b _ _ = (b, False)

-- | The permuteEquiv Function determines if a context is a permutation
-- of another, if so it returns true.
permuteEquiv :: Context -> Context -> Bool
permuteEquiv [] []      = True
permuteEquiv (v:vs) ctx =
  case v `lookup` ctx of
    Nothing -> False
    Just t  -> let ctx' = ctx \\ [(s,t)] in permuteEquiv vs ctx'
permuteEquiv _ _        = False