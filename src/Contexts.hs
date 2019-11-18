--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/17/19                --
--------------------------------------------

module Contexts
  (
    Context(..)
  , push
  , getType
  , pushAll
  , getFreeVars
  , getFreeVarsT
  
  ) where


-- Foriegn Imports
import Data.List ((\\), subsequences, reverse, zip)
import Data.Function (flip)

-- Domestic Imports
import Primitives (Type(..), Term(..))


-- | Contexts are merely lists of 'type judgements', which are themselves
-- comprised of pairs of strings and types.
type Context = [(String, Type)]


-- | The push function is simply concatenation of a judgement. Observe that
-- the 'first' judgement in the context is the most recently pushed.
push :: Context -> (String, Type) -> Context
push ctx p = p : ctx

-- | The pushAll function pushes all of the judgements onto the context.
-- Example:
--   pushAll [] [("a", I), ("b", I)] ==> [("b", I), ("a", I)]
--
pushAll :: Context -> [(String, Type)] -> Context
pushAll ctx []     = ctx
pushAll ctx (p:ps) = push ctx p

-- | The getType function returns the type associated with the string
-- provided. If the string is not found in the context, then it returns
-- 'Nothing'.
getType :: Context -> String -> Maybe Type
getType = flip lookup

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
getFreeVars (AppT e t)        = getFreeVars e ++ getFreeVarsT t

-- | The getFreeVarsT function takes a type and returns the list of free
-- variables in the type.
getFreeVarsT :: Type -> [String]
getFreeVarsT (TVar s)     = [s]
getFreeVarsT Unit         = []
getFreeVarsT (Univ _)     = []
getFreeVarsT (Pi s t1 t2) = (getFreeVarsT t1 ++ getFreeVarsT t2) \\ [s]
getFreeVarsT (Prod t1 t2) = getFreeVarsT t1 ++ getFreeVarsT t2