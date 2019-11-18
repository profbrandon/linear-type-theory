--------------------------------------------
-- Author:        Brandon Harrington      --
-- Last Updated:  11/17/19                --
--------------------------------------------

module Display
  (
    showType
  , showTerm
  , showCtx

  ) where


-- Domestic Imports
import Contexts(Context(..), push, pushAll, getFreeVars, getFreeVarsT)
import Primitives(Type(..), Term(..), Judgement(..))


-- Instance Declarations
instance Show Term where
  show e = showTerm [] e

instance Show Type where
  show t = showType [] t

instance Show Judgement where
  show j = showJudge [] j


-- | The showCtx function converts a context to a string representation.
showCtx :: Context -> String
showCtx []          = "-"
showCtx [(s, t)]    = s ++ " : " ++ show t
showCtx ((s, t):ps) = showCtx [(s, t)] ++ ", " ++ showCtx ps

-- | The showType function converts a given type into its string
-- equivalent using the context provided. (The context is not used but
-- is there to allow easy extension to dependent types).
showType :: Context -> Type -> String
showType ctx (TVar s)       = s
showType ctx Unit           = "I"
showType ctx (Univ i)       = "U@" ++ show i
showType ctx p@(Pi s t1 t2) = 
  if s `elem` (getFreeVarsT t2) then 
    let (vars, ctx', t') = showVarsT ctx p
    in "forall " ++ vars ++ ". " ++ showType ctx t'
  else
    showTypeRightA ctx t1 ++ " -+ " ++ showType ctx t2 
showType ctx (Prod t1 t2) = showTypeGroup ctx t1 ++ " @ " ++ showTypeGroup ctx t2

-- | The showTypeRightA function wraps types in parenthesis if they are
-- products or arrows and are the hypothesis of an implication. Otherwise,
-- the function simply shows the type.
showTypeRightA :: Context -> Type -> String
showTypeRightA ctx a@(Pi _ _ _) = "(" ++ showType ctx a ++ ")"
showTypeRightA ctx p@(Prod _ _) = "(" ++ showType ctx p ++ ")"
showTypeRightA ctx t            = showType ctx t

-- | The showTypeGroup function wraps any types that are "groups" of other
-- types in parenthesis. As of right now, this amounts to non-unit types. 
showTypeGroup :: Context -> Type -> String
showTypeGroup ctx Unit     = showType ctx Unit
showTypeGroup ctx (TVar s) = showType ctx $ TVar s
showTypeGroup ctx (Univ i) = showType ctx $ Univ i
showTypeGroup ctx t        = "(" ++ showType ctx t ++ ")"

-- | The showTerm function converts a given term into its string equivalent
-- using the context provided.
showTerm :: Context -> Term -> String
showTerm ctx (Var s)           = s
showTerm _   Star              = "*"
showTerm ctx (RecI t e1 e2)    = "recI (" ++ showType ctx t ++ ", " ++ showTerm ctx e1 ++ ", " ++ showTerm ctx e2 ++ ")"
showTerm ctx (Pair e1 e2)      = showTermGroup ctx e1 ++ " @ " ++ showTermGroup ctx e2
showTerm ctx (RecPair t e1 e2) = "rec@ (" ++ showType ctx t ++ ", " ++ showTerm ctx e1 ++ ", " ++ showTerm ctx e2 ++ ")"
showTerm ctx l@(Lambda _ _ _)  = "\\" ++ vars ++ ". " ++ showTerm ctx' e' where (vars, ctx', e') = showVars ctx l
showTerm ctx (App e1 e2)       = showTermRightA ctx e1 ++ " " ++ showTermGroup ctx e2
showTerm ctx (AppT e t)        = showTermRightA ctx e ++ " " ++ showTypeGroup ctx t

-- | The findVars function finds all variables declared in consecutive
-- lambda expressions in a term, and finds the first non-lambda term.
-- The function then returns all of the typing judgements for the
-- variables and the bottom term.
findVars :: Term -> ([(String, Type)], Term)
findVars (Lambda s t e) = ((s, t):vs, e') where (vs, e') = findVars e
findVars e              = ([], e)

findVarsT :: Type -> ([(String, Type)], Type)
findVarsT p@(Pi s t1 t2) = 
  if s `elem` getFreeVarsT t2 then
    ((s, t1):vs, t2') 
  else
    ([], p)
  where (vs, t2') = findVarsT t2
findVarsT t            = ([], t)

-- | The collectVars function takes a list of typing judgements and
-- groups them via type.
collectVars :: [(String, Type)] -> [([String], Type)]
collectVars []         = []
collectVars [(s,t)]    = [([s],t)]
collectVars ((s,t):ls) = if t == t' then (s:ss, t'):vs else ([s],t):r where r@((ss, t'):vs) = collectVars ls

-- | The showVarsHelp function is the helper function for showVars. It
-- takes a boolean signalling whether it is at the first lambda and a
-- list of collected type judgements. It then returns the string rep-
-- resentation of the collected type judgements.
showVarsHelp :: Bool -> [([String], Type)] -> String
showVarsHelp _    []          = ""
showVarsHelp b ((ss,t):ls) 
  | b     = back 
  | not b = ", " ++ back
  where back = foldl (++) "" (fmap (\s -> s ++ " ") ss) ++ ": " ++ show t ++ showVarsHelp False ls

-- | The showVars function takes a context and a term, finds the
-- variables that are immediately declared in 'e', collects the found
-- variables, converts these to a string, and returns the string, the
-- updated context, and the first non-lambda subterm.
showVars :: Context -> Term -> (String, Context, Term)
showVars ctx e = (showVarsHelp True vs', pushAll ctx vs, e')
  where
    vs'      = collectVars vs
    (vs, e') = findVars e

showVarsT :: Context -> Type -> (String, Context, Type)
showVarsT ctx t = (showVarsHelp True vs', pushAll ctx vs, e')
  where
    vs'      = collectVars vs
    (vs, e') = findVarsT t

-- | The showTermRightA function wraps a term in parenthesis if it is
-- a lambda in the left hand side of an application.
showTermRightA :: Context -> Term -> String
showTermRightA ctx l@(Lambda _ _ _) = "(" ++ showTerm ctx l ++ ")"
showTermRightA ctx t                = showTerm ctx t

-- | The showTermGroup function wraps a term in parenthesis to avoid
-- ambiguity in pair terms.
showTermGroup :: Context -> Term -> String
showTermGroup ctx p@(Pair _ _)     = "(" ++ showTerm ctx p ++ ")"
showTermGroup ctx l@(Lambda _ _ _) = "(" ++ showTerm ctx l ++ ")"
showTermGroup ctx a@(App _ _)      = "(" ++ showTerm ctx a ++ ")"
showTermGroup ctx t                = showTerm ctx t

-- | The showJudge function converts judgements into their string
-- counterparts using the given context.
showJudge :: Context -> Judgement -> String
showJudge ctx (Define s (Left  e)) = "Define " ++ s ++ " := " ++ showTerm ctx e ++ " ;"
showJudge ctx (Define s (Right t)) = "Define " ++ s ++ " := " ++ showType ctx t ++ " ;"
showJudge ctx (Typeof (Left  e))   = "Typeof " ++ showTerm ctx e ++ " ;"
showJudge ctx (Typeof (Right t))   = "Typeof " ++ showType ctx t ++ " ;"
showJudge ctx (Normal e)           = "Normal " ++ showTerm ctx e ++ " ;"