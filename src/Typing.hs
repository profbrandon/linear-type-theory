--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/14/19                --
--------------------------------------------

module Typing
  ( 
    typeof 
  , typeof0
  , typeofT
  , typeofT0
    
  ) where


-- Foriegn Imports
import Data.List(permutations, subsequences, (\\))

-- Domestic Imports
import Contexts(Context(..), push)
import Primitives(Type(..), Term(..))
import Display(showCtx, showType)


-- | The join function takes an error message and a list of pairs of either
-- strings or types and compresses these to the error message if no pairs were
-- both types, or returns the pair of types. This is used in determining if any
-- subcontexts were well-behaved in the sense that they provided a typing
-- judgement for two terms.
join :: String -> [(Either String Type, Either String Type)] -> Either String (Type, Type)
join s []                        = Left s
join s ((Right t1, Right t2):ls) = Right (t1, t2)
join s (_:ls)                    = join s ls

-- | The getSubCtxs function takes a context and returns all pairs of sub-
-- contexts (i.e. disjoint but their union is the original context).
getSubCtxs :: Context -> [(Context, Context)]
getSubCtxs ctx = zip total total'
  where
    total = foldl (++) [] (fmap permutations (subsequences ctx))
    total' = fmap (\ctx' -> ctx \\ ctx') total

-- | The findViableSubs function takes an error message, a context, two terms,
-- and computes whether any subcontexts type both of the terms. If this is not
-- the case then the error message is returned. This function is needed due to
-- some of the typing rules for the linear lambda calculus. Specifically, those
-- for function application, pair creation, and recursion.
findViableSubs :: String -> Context -> Term -> Term ->  Either String (Type, Type)
findViableSubs s ctx e1 e2 = join s $ fmap (\(a,b) -> (typeof0 a e1, typeof0 b e2)) (getSubCtxs ctx)

-- | The typeof function returns either an error message or the type of a term
-- (in the empty context).
typeof :: Term -> Either String Type
typeof = typeof0 []

-- | The typeof0 function is a helper function for typeof0 that takes a context
-- and a term and computes either an error message or a typing for the term in
-- the context.
typeof0 :: Context -> Term -> Either String Type
typeof0 _ Star = return Unit

typeof0 ctx r@(RecI t e1 e2) = do
  let pair = findViableSubs ("All subcontexts failed for the recursion '" ++ show r ++ "'") ctx e1 e2
  case pair of
    Left e -> Left e
    Right (t1, t2) ->
      if t1 == t then
        if t2 == Unit then
          return t
        else
          Left "Unit recursion expected the second argument to be of type 'Unit'"
      else
        Left $ "Unit recursion expected the first argument to be of type " ++ showType ctx t

typeof0 ctx p@(Pair e1 e2) = do
  let pair = findViableSubs ("All subcontexts failed for the pair '" ++ show p ++ "'") ctx e1 e2
  case pair of
    Left  e        -> Left e
    Right (t1, t2) -> return (Prod t1 t2)

typeof0 ctx r@(RecPair t e1 e2) = do
  let pair = findViableSubs ("All subcontexts failed for recursion '" ++ show r ++ "'") ctx e1 e2
  case pair of
    Left e -> Left e
    Right (t1, t2) -> 
      case t2 of
        Prod t21 t22 -> 
          case t1 of
            Arrow t11 (Arrow t12 t13) ->
              if t13 == t then
                if t11 == t21 && t12 == t22 then
                  return t
                else
                  Left "Pair recursion expected the pair and function types to agree"
              else
                Left "Pair recursion expected the output types to match"
            _ -> Left $ "Pair recursion expected the first argument to have type " ++ show (Arrow t21 (Arrow t22 t)) ++ " not " ++ show t1
        _ -> Left "Pair recursion expected the second argument to be a pair"

typeof0 []       (Var v) = Left $ "When searching for '" ++ v ++ "', the context was discovered to be empty"
typeof0 [(s, t)] (Var v) = if s == v then return t else Left $ "Context did not contain the variable '" ++ v ++ "'"
typeof0 ctx      (Var v) = Left $ "When looking in the context G := (" ++ showCtx ctx ++ ") for the variable '" ++ v ++ "' the context contained more than one item"

typeof0 ctx (Lambda s t e) = do
  t' <- typeof0 (push ctx (s, t)) e
  return (Arrow t t')

typeof0 ctx a@(App e1 e2) = do
  let pair = findViableSubs ("All subcontexts failed for the application '" ++ show a ++ "'") ctx e1 e2
  case pair of
    Left e -> Left e
    Right (t1, t2) ->
      case t1 of
        Arrow t11 t12 ->
          if t11 == t2 then
            return t12
          else
            Left "Function application required function input type to be the same as the argument's"
        _ -> Left "Expected function type as the left part of an application"


-- | The typeofT computes the type of the type.
typeofT :: Type -> Either String Type
typeofT = typeofT0 []

-- | The typeofT0 function is the helper function for typeofT.
typeofT0 :: Context -> Type -> Either String Type
typeofT0 _   (Univ i) = return (Univ $ i + 1)
typeofT0 _   Unit     = return (Univ 1)

typeofT0 ctx (Arrow t1 t2) = do
  u1 <- typeofT0 ctx t1
  u2 <- typeofT0 ctx t2
  case (u1,u2) of
    (Univ i, Univ j) -> return (Univ $ max i j)

typeofT0 ctx (Prod t1 t2) = do
  u1 <- typeofT0 ctx t1
  u2 <- typeofT0 ctx t2
  case (u1,u2) of
    (Univ i, Univ j) -> return (Univ $ max i j)