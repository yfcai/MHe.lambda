{-# LANGUAGE CPP #-}

-- An exercise in evaluating abstract syntax trees
-- of untyped lambda calculus in de-Bruijn notations

module LAM (
) where

import qualified Data.Map as Map
import qualified Data.Set as Set

-- Unchecked disciplinary requirement:
-- var(iables) = lower case letters
-- con(stants) = upper case letters

-- de-Bruijn levels
data Llambda
 = Lcon Char
 | Lvar Int
 | Llam Char Llambda
 | Lapp Llambda Llambda

-- de-Bruijn indices
data Ilambda
 = Icon Char
 | Ivar Int
 | Ilam Char Ilambda
 | Iapp Ilambda Ilambda

class Lambda a where
 -- reduction    - reduce formula 1 step and report whether it changed
 reduce :: a -> (a, Bool)
 -- substitution - replace Int0 with a1 in a2 to yield a3
 subst  :: Int -> a -> a -> a

instance Lambda Llambda where reduce = lreduce ; subst = lsubst
instance Lambda Ilambda where reduce = ireduce ; subst = isubst

-- BEGIN expressions to test evaluation in console
-- y = λf. (λx. f (x x)) (λx. f (x x))
-- Indices λ (λ 1 (0 0)) (λ 1 (0 0))
-- Levels  λ (λ 0 (1 1)) (λ 0 (1 1))
iy    = let omg = Ilam 'x' (Iapp (Ivar 1) (Iapp (Ivar 0) (Ivar 0)))
        in Ilam 'f' (Iapp omg omg)
ly    = let omg = Llam 'x' (Lapp (Lvar 0) (Lapp (Lvar 1) (Lvar 1)))
        in Llam 'f' (Lapp omg omg)
ia    = Ilam 'x' (Ilam 'x' (Iapp (Ivar 1) (Ivar 0)))
la    = Llam 'x' (Llam 'x' (Lapp (Lvar 0) (Lvar 1)))
itru  = Ilam 't' (Ilam 'f' (Ivar 1))
ifls  = Ilam 't' (Ilam 'f' (Ivar 0))
ipair = Ilam 'f' (Ilam 's' (Ilam 'b'
        (Iapp (Iapp (Ivar 0) (Ivar 2)) (Ivar 1))))
-- such compositionality are not enjoyed by de-Bruijn levels
-- even if de-Bruijn indices can only do it reliably on combinators
iid   = Ilam 'x' (Ivar 0)
ifst  = Ilam 'p' (Iapp (Ivar 0) itru)
isnd  = Ilam 'p' (Iapp (Ivar 0) ifls)
iexp  = Iapp ifst (Iapp (Iapp ipair (Icon 'V')) (Icon 'W'))
iexp1 = Ilam 'x' (Iapp (Icon 'F') iexp)
iexp2 = Iapp ifls (Icon 'V')
iexp3 = Iapp iid iid
iexp4 = Ilam 'x' $ Ilam 'x' $ Ilam 'y' $ Ivar 0
iexp5 = Ilam 'f' $ Iapp iid (Ivar 0)
-- therefore we make level-terms from index-terms
lid   = i_to_l iid
ltru  = i_to_l itru
lfls  = i_to_l ifls
lexp  = i_to_l iexp
lexp1 = i_to_l iexp1
lexp2 = i_to_l iexp2
lexp3 = i_to_l iexp3
-- END expressions to test evaluation in console

instance Show Llambda where
 show = let
  to_s :: Map.Map Int [Char] -> Set.Set Char -> Int -> Llambda -> [Char]
  to_s names taken level body = case body of
   Lcon c   -> c:[]
   Lvar i   -> Map.findWithDefault ('?':show i) i names
   Llam x s -> let (x_name , new_taken) = if Set.member x taken
                   then (x : show level , taken              )
                   else (x : []         , Set.insert x taken )
               in "(λ" ++ x_name ++ ". "
                  ++ to_s (Map.insert level x_name names)
                          new_taken     (level + 1)     s ++ ")"
   Lapp s t -> let print = to_s names taken level in case t of
               Lapp _ _   -> print s ++ " (" ++ print t ++ ")"
               otherwise -> print s ++ ' ' : print t
  in to_s Map.empty Set.empty 0


-- convert de-Bruijn-index notation to -level notation
i_to_l :: Ilambda -> Llambda
i_to_l = loop (-1) where
 loop _     (Icon c  ) = Lcon c
 loop depth (Ivar i  ) = Lvar (depth - i)
 loop depth (Ilam x s) = Llam x (loop (depth + 1) s)
 loop depth (Iapp s t) = Lapp (loop depth s) (loop depth t)

instance Show Ilambda where
 show = show . i_to_l -- print by conversion to de-Bruijn-level form

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

