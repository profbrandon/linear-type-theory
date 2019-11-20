--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/19/19                --
--------------------------------------------

module Contexts
  (
    Context(..)

  , push, pushAll

  , getType

  , getFreeVars, getFreeVarsT

  , getSubCtx
  , isUnivCtx
  
  ) where


-- Foriegn Imports
import Data.List ( (\\), permutations, subsequences, reverse, zip, union )
import Data.Function ( flip )

-- Domestic Imports
import Primitives ( Type(..), Term(..) )


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
pushAll :: Context -> [(String, Type)] -> Context
pushAll = foldl push

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
getFreeVars (RecI t e1 e2)    = getFreeVarsT t `union` getFreeVars e1 `union` getFreeVars e2
getFreeVars (Pair e1 e2)      = getFreeVars e1 `union` getFreeVars e2
getFreeVars (RecPair t e1 e2) = getFreeVarsT t `union` getFreeVars e1 `union` getFreeVars e2
getFreeVars (Lambda s t e)    = getFreeVarsT t `union` (getFreeVars e \\ [s])
getFreeVars (App e1 e2)       = getFreeVars e1 `union` getFreeVars e2
getFreeVars (AppT e t)        = getFreeVars e `union` getFreeVarsT t

-- | The getFreeVarsT function takes a type and returns the list of free
-- variables in the type.
getFreeVarsT :: Type -> [String]
getFreeVarsT (TVar s)     = [s]
getFreeVarsT Unit         = []
getFreeVarsT (Univ _)     = []
getFreeVarsT (Pi s t1 t2) = getFreeVarsT t1 `union` (getFreeVarsT t2 \\ [s])
getFreeVarsT (Prod t1 t2) = getFreeVarsT t1 `union` getFreeVarsT t2

-- | The getSubCtx function takes a context and a list of variables. If there
-- is a variable that is not in the context, then the function fails with a
-- value of Nothing. Otherwise, a pair of the old context (minus the taken
-- values) and the new sub context are returned.
getSubCtx :: Context -> [String] -> Maybe (Context, Context)
getSubCtx ctx [] = Just (ctx, [])
getSubCtx ctx (n:ns) = do
  t <- n `lookup` ctx
  case t of
    Univ _ -> do
      (ctx', back) <- getSubCtx ctx ns
      return (ctx', (n,t):back)
    _      -> do
      let ctx' = ctx \\ [(n,t)]
      (ctx'', back) <- getSubCtx ctx' ns
      return (ctx'', (n,t):back)

-- | The isUnivCtx function checks if the context is formed purely out of
-- "higher-level types." This is to accomodate the asymmetry between types
-- and terms (term variables must be used once and only once, whereas type
-- variables can be used multiple times).
isUnivCtx :: Context -> Bool
isUnivCtx ctx = and (map isHLType ctx') where ctx' = (snd . unzip) ctx

isHLType :: Type -> Bool
isHLType (Univ _) = True
isHLType _        = False