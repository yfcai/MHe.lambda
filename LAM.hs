-- data types for lambda calculus, their on-screen representation
-- and example expressions

module LAM where

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

{--- "polymorphic" pattern matching 
class CVAL a where
 cval :: ((Char -> a) -> Char -> b) ->
         ((Int -> a) -> Int -> b) ->
         ((a -> a -> a) -> a -> a -> b) ->
         ((Char -> a -> a) -> Char -> a -> b) -> (a -> b)

instance CVAL Llambda where
 cval fc fv fa fl body = case body of
  Lcon c   -> fc Lcon c
  Lvar i   -> fv Lvar i
  Lapp s t -> fa Lapp s t
  Llam x s -> fl Llam x s

instance CVAL Ilambda where
 cval fc fv fa fl body = case body of
  Icon c   -> fc Icon c
  Ivar i   -> fv Ivar i
  Iapp s t -> fa Iapp s t
  Ilam x s -> fl Ilam x s
-}

instance Show Llambda where
 show = let
  to_s :: Map.Map Int [Char] -> Set.Set Char -> Int -> Llambda -> [Char]
  to_s names taken level body = case body of
   Lcon c   -> c:[]
   Lvar i   -> Map.findWithDefault ('?':show i) i names
   Llam x s ->    let (x_name , new_taken) = if Set.member x taken
                      then (x : show level , taken              )
                      else (x : []         , Set.insert x taken )
                  in "λ" ++ x_name ++ ". "
                     ++ to_s (Map.insert level x_name names)
                             new_taken (level + 1) s

   Lapp s t -> let print = to_s names taken level
                   paren = \x -> '(' : print x ++ ")"
                   s_str = (case s of Llam _ _  -> paren
                                      otherwise -> print) s
                   t_str = (case t of Llam _ _  -> paren
                                      Lapp _ _  -> paren
                                      otherwise -> print) t
               in s_str ++ ' ' : t_str
  in to_s Map.empty Set.empty 0


-- convert de-Bruijn-index notation to -level notation
i_to_l :: Ilambda -> Llambda
i_to_l = loop (-1) where
 loop _     (Icon c  ) = Lcon c
 loop depth (Ivar i  ) = Lvar (depth - i)
 loop depth (Ilam x s) = Llam x (loop (depth + 1) s)
 loop depth (Iapp s t) = Lapp (loop depth s) (loop depth t)

-- print indices by conversion to de-Bruijn-level form
instance Show Ilambda where
 show = show . i_to_l

-- expressions to test evaluation in console
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
irep  = (Ilam 'x' $ Iapp (Ivar 0) (Ivar 0))
ifst  = Ilam 'p' (Iapp (Ivar 0) itru)
isnd  = Ilam 'p' (Iapp (Ivar 0) ifls)
iexp  = Iapp ifst (Iapp (Iapp ipair (Icon 'V')) (Icon 'W'))
iexp1 = Ilam 'x' (Iapp (Icon 'F') iexp)
iexp2 = Iapp ifls (Icon 'V')
iexp3 = Iapp iid iid
iexp4 = Ilam 'x' $ Ilam 'x' $ Ilam 'y' $ Ivar 0
iexp5 = Ilam 'f' $ Iapp iid (Ivar 0)
iexp6 = Iapp (Ilam 'x' $ Iapp (Ivar 0) (Ivar 0))
             (Iapp iid (Icon 'W'))
iexp7 = Ilam 'x' $ Ilam 'y' $ Ilam 'z'
      $ Iapp (Iapp (Ivar 2) (Ivar 0)) (Iapp (Ivar 1) (Ivar 0))
iexp8 = Ilam 'x' $ Ilam 'y' $ Iapp (Ivar 1) (Ivar 0)
-- therefore we make level-terms from index-terms
lid   = i_to_l iid
lrep  = i_to_l irep
ltru  = i_to_l itru
lfls  = i_to_l ifls
lfst  = i_to_l ifst
lsnd  = i_to_l isnd
lexp  = i_to_l iexp
lexp1 = i_to_l iexp1
lexp2 = i_to_l iexp2
lexp3 = i_to_l iexp3
lexp4 = i_to_l iexp4
lexp5 = i_to_l iexp5
lexp6 = i_to_l iexp6
lexp7 = i_to_l iexp7
lexp8 = i_to_l iexp8
