--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/14/19                --
--------------------------------------------

module Contexts
  (
    Context(..)
  , push
  , getType
  , pushAll
  
  ) where


-- Foriegn Imports
import Data.List (subsequences, reverse, zip)
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