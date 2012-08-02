-- An exercise in evaluating abstract syntax trees
-- of untyped lambda calculus in de-Bruijn notations

module EVA where

import LAM

class Lambda a where
 -- reduction    - reduce formula 1 step and report whether it changed
 reduce :: a -> (a, Bool)
 -- substitution - replace Int0 with a1 in a2 to yield a3
 subst  :: Int -> a -> a -> a

instance Lambda Llambda where reduce = lreduce ; subst = lsubst
instance Lambda Ilambda where reduce = ireduce ; subst = isubst

-- change level of bound variables (i. e., those whose level EXCEEDS
-- the threshold) by an amount
ladjust :: Int -> Int -> Llambda -> Llambda
ladjust threshold amount formula = case formula of
 Lcon c   -> formula
 Lvar i   -> if i > threshold then Lvar (i + amount) else formula
 Lapp s t -> let f = ladjust threshold amount in Lapp (f s) (f t)
 Llam x s -> Llam x (ladjust threshold amount s)

-- change indices of free variables (i. e., those whose index is AT LEAST
-- the threshold) by an amount
iadjust :: Int -> Int -> Ilambda -> Ilambda
iadjust threshold amount formula = case formula of
 Icon c   -> formula
 Ivar i   -> if i >= threshold then Ivar (i + amount) else formula
 Iapp s t -> let f = iadjust threshold amount in Iapp (f s) (f t)
 Ilam x s -> Ilam x (iadjust (threshold + 1) amount s)

{- REMARK
   Interestingly, it doesn't matter whether the comparisons in ladjust
   and iadjust are > or >=. In a beta redex ((λx. t) s), the free variables
   of s with the greatest level and smallest indices occupies an echelon of
   its own, whose counterpart is taken by λx and does not appear in t. It
   is therefore irrelevant whether or not those free variables have their
   levels/indices adjusted; in either case level/index clashes are
   impossible, and any changes will be reversed by the second application
   of ladjust/iadjust. The comparison sign is strict for iadjust and non-
   strict for ladjust so that logically the bound variables of t have their
   levels adjusted and the free variables of t have their index adjusted.
-}

-- substitute at level-i the level-i variables in t by s
-- we assume that the bound variables of s have levels greater than i
lsubst :: Int -> Llambda -> Llambda -> Llambda
lsubst i s body = sub s body where
 sub _ (Lcon c  ) = Lcon c
 sub s (Lvar j  ) = if i == j then s else (Lvar j)
 sub s (Llam x t) = Llam x (sub (ladjust i 1 s) t)
 sub s (Lapp t u) = Lapp (sub s t) (sub s u)

-- substitute in body (last argument) the variable with index i by s
-- outer variables of s with indices 0 or more are free
isubst :: Int -> Ilambda -> Ilambda -> Ilambda
isubst _ _ (Icon c  ) = Icon c
isubst i s (Ivar j  ) = if i == j then s else (Ivar j)
isubst i s (Ilam x t) = Ilam x (isubst (i + 1) (iadjust 0 1 s) t)
isubst i s (Iapp t u) = let f = isubst i s in Iapp (f t) (f u)

lreduce :: Llambda -> (Llambda, Bool)
lreduce = lstep (-1) where
 -- result = (formula-after-1-step, formula-was-reducible-before-the-step)
 -- first argument of lstep is depth at which substitution is carried out
 -- the necessity to keep track of depth may be the reason that indices
 -- are more popular than levels despite the latter's intuitive appeal
 -- and close ties to named variables themselves
 lstep :: Int -> Llambda -> (Llambda, Bool)
 lstep depth (Lapp (Llam _ t) s) =
  (ladjust depth (-1) (lsubst (depth + 1) (ladjust depth 1 s) t), True)
 lstep depth (Lapp s t) = let
  (new_s, s_done) = lstep depth s
  (new_t, t_done) = lstep depth t
  in if s_done then (Lapp new_s t, True) else (Lapp s new_t, t_done)
 lstep depth (Llam x s) = let
  (new_s, s_done) = lstep (depth + 1) s
  in (Llam x new_s, s_done)
 lstep depth others = (others, False)
 
ireduce :: Ilambda -> (Ilambda, Bool)
ireduce (Iapp (Ilam _ t) s) =
 (iadjust 0 (-1) (isubst 0 (iadjust 0 1 s) t), True)
ireduce (Iapp s t) = let
 (new_s, s_done) = ireduce s
 (new_t, t_done) = ireduce t
 in if s_done then (Iapp new_s t, True) else (Iapp s new_t, t_done)
ireduce (Ilam x s) = let
 (new_s, s_done) = ireduce s
 in (Ilam x new_s, s_done)
ireduce others = (others, False)

eval :: Lambda a => a -> a
eval s = let (new_s, unfinished) = reduce s
         in if unfinished then eval new_s else new_s

eval_show :: (Show a, Lambda a) => a -> IO ()
eval_show s = print s >>
 let (new_s, unfinished) = reduce s
 in if unfinished then eval_show new_s else return ()

