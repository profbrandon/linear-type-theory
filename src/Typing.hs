--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/19/19                --
--------------------------------------------

module Typing
  ( 
    typeof 
  , typeof0
  , typeofT
  , typeofT0
    
  ) where


-- Foriegn Imports
import Data.List ( (\\) )

-- Domestic Imports
import Contexts ( Context(..), push, getFreeVars, getSubCtx, isUnivCtx )
import Primitives ( Type(..), Term(..) )
import Display ( showCtx, showType )
import Eval ( subAllT )
import Equiv ( arrowEquiv )


-- | The join function takes an error message and a list of pairs of either
-- strings or types and compresses these to the error message if no pairs were
-- both types, or returns the pair of types. This is used in determining if any
-- subcontexts were well-behaved in the sense that they provided a typing
-- judgement for two terms.
join :: String -> [(Either String Type, Either String Type)] -> Either String (Type, Type)
join s []                        = Left s
join s ((Right t1, Right t2):ls) = Right (t1, t2)
join s (_:ls)                    = join s ls

-- | The findViableSubs function takes an error message, a context, two terms,
-- and computes whether any subcontexts type both of the terms. If this is not
-- the case then the error message is returned. This function is needed due to
-- some of the typing rules for the linear lambda calculus. Specifically, those
-- for function application, pair creation, and recursion.
findViableSubs :: Context -> Term -> Term ->  Either String (Context, Context)
findViableSubs ctx e1 e2 = do
  let vs1  = getFreeVars e1 
      vs2  = getFreeVars e2
  case getSubCtx ctx vs1 of
    Nothing           -> Left $ "The variable(s) " ++ show vs1 ++ " were not contained in the context (" ++ showCtx ctx ++ ")"
    Just (ctx', sub1) ->
      case getSubCtx ctx' vs2 of
        Nothing -> Left $ "The variable(s) " ++ show vs2 ++ " were not contained in the context (" ++ showCtx ctx' ++ ")"
        Just (ctx'', sub2) ->
          if isUnivCtx ctx'' then
            return (sub1, sub2)
          else
            Left $ "There are still term variables in the context (" ++ showCtx ctx'' ++ ") that must occur"

-- | The typeof function returns either an error message or the type of a term
-- (in the empty context).
typeof :: Term -> Either String Type
typeof t =
  case getFreeVars t of
    [] -> typeof0 [] t
    vs -> Left $ "The term '" ++ show t ++ "' has unbound variables: " ++ show vs

-- | The typeof0 function is a helper function for typeof0 that takes a context
-- and a term and computes either an error message or a typing for the term in
-- the context.
typeof0 :: Context -> Term -> Either String Type
typeof0 ctx  Star = 
  if isUnivCtx ctx then
    return Unit
  else
    Left $ "When deciding the type of '*', the context contained term variables."

typeof0 ctx r@(RecI t e1 e2) = do
  (ctx1, ctx2) <- findViableSubs ctx e1 e2
  t1 <- typeof0 ctx1 e1
  t2 <- typeof0 ctx2 e2
  if t1 `arrowEquiv` t then
    if t2 == Unit then
      return t
    else
      Left "Unit recursion expected the second argument to be of type 'Unit'"
  else
    Left $ "Unit recursion expected the first argument to be of type " ++ showType ctx t

typeof0 ctx p@(Pair e1 e2) = do
  (ctx1, ctx2) <- findViableSubs ctx e1 e2
  t1 <- typeof0 ctx1 e1
  t2 <- typeof0 ctx2 e2
  return (Prod t1 t2)

typeof0 ctx r@(RecPair t e1 e2) = do
  (ctx1, ctx2) <- findViableSubs ctx e1 e2
  t1 <- typeof0 ctx1 e1
  t2 <- typeof0 ctx2 e2
  case t2 of
    Prod t21 t22 -> 
      case t1 of
        Pi _ t11 (Pi _ t12 t13) ->
          if t13 `arrowEquiv` t then
            if t11 `arrowEquiv` t21 && t12 `arrowEquiv` t22 then
              return t
            else
              Left "Pair recursion expected the pair and function types to agree"
          else
            Left "Pair recursion expected the output types to match"
        _ -> Left $ "Pair recursion expected the first argument to have type " 
          ++ show (Pi "_" t21 (Pi "_" t22 t)) ++ " not " ++ show t1
    _ -> Left "Pair recursion expected the second argument to be a pair"

typeof0 []           (Var v) = Left $ "When searching for '" ++ v ++ "', the context was discovered to be empty"

typeof0 ctx@[(s, t)] (Var v) = 
  if s == v then 
    return t
  else 
    Left $ "The context G := (" ++ showCtx ctx ++ ") did not contain the variable '" ++ v ++ "'"

typeof0 ctx          (Var v) =
  case v `lookup` ctx of
    Nothing -> Left $ "The context G := (" ++ showCtx ctx ++ ") did not contain the variable '" ++ v ++ "'"
    Just  t -> 
      if isUnivCtx (ctx \\ [(v, t)]) then
        return t
      else
        Left $ "When looking in the context G := (" ++ showCtx ctx ++ ") for the variable '" 
          ++ v ++ "' the context contained more than one term judgement"

typeof0 ctx (Lambda s t e) = do
  t' <- typeof0 (push ctx (s, t)) e
  return (Pi s t t')

typeof0 ctx a@(App e1 e2) = do
  (ctx1, ctx2) <- findViableSubs ctx e1 e2
  t1 <- typeof0 ctx1 e1
  t2 <- typeof0 ctx2 e2
  case t1 of
    Pi _ t11 t12 ->
      if t11 `arrowEquiv` t2 then
        return t12
      else
        Left $ "Expected the types '" ++ showType ctx t11 ++ "' and '" 
          ++ showType ctx t2 ++ "' to match in an application"
    _            -> Left "Expected function type as the left part of an application"

typeof0 ctx a@(AppT e t) = do
  t1 <- typeof0 ctx e
  t2 <- typeofT0 ctx t
  case t1 of
    Pi s (Univ i) t11 -> 
      case t2 of
        Univ j -> 
          if i >= j then 
            return $ subAllT t11 [(s, Right t)]
          else 
            Left "Universe level mismatch"
    Pi _ t' _         -> Left $ "The lambda on the left should expect a type argument, not one of type '" 
                          ++ showType ctx t' ++ "'"
    _                 -> Left "Expected lambda as the left part of a type application"

-- | The typeofT computes the type of the type.
typeofT :: Type -> Either String Type
typeofT = typeofT0 []

-- | The typeofT0 function is the helper function for typeofT.
typeofT0 :: Context -> Type -> Either String Type
typeofT0 _   (Univ i) = return (Univ $ i + 1)
typeofT0 _   Unit     = return (Univ 1)

typeofT0 ctx (TVar s) = 
  case s `lookup` ctx of
    Nothing -> Left $ "The context G := (" ++ showCtx ctx ++ ") does not contain the variable '" ++ s ++ "'"
    Just  t -> return t

typeofT0 ctx (Pi s t1 t2) = do
  u1 <- typeofT0 ctx t1
  u2 <- typeofT0 (push ctx (s, t1)) t2
  case (u1,u2) of
    (Univ i, Univ j) -> return (Univ $ max i j)

typeofT0 ctx (Prod t1 t2) = do
  u1 <- typeofT0 ctx t1
  u2 <- typeofT0 ctx t2
  case (u1,u2) of
    (Univ i, Univ j) -> return (Univ $ max i j)