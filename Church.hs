{-# OPTIONS_GHC -XRankNTypes -XImpredicativeTypes          #-}
{-# OPTIONS_GHC -XUndecidableInstances -XFlexibleInstances #-}

-- Church Booleans
-- > if condition then true-expr else false-expr
-- translates to
-- > condition true-expr false-expr
--
-- > f x | cond0     = expr0
-- >     | cond1     = expr1
-- >     | cond2     = expr2
-- >     | otherwise = expr3
-- translates to
-- > f x = cond0 expr0 $
-- >       cond1 expr1 $
-- >       cond2 expr2 $
-- >             expr3

module Church
( Cbool
, if'
, true
, false
, Ceq, Cord
, (.==), (./=), (.<), (.<=), (.>=), (.>)
, (.&&), (.||)
, cnot
) where

type Cbool = forall a. a -> a -> a

true  :: Cbool
false :: Cbool
true  x y = x
false x y = y

if' :: Bool -> Cbool
if' True  = true
if' False = false

infix  4  .==, ./=, .<, .<=, .>=, .>
infixr 3  .&&
infixr 2  .||

class Ceq a where
 (.==) :: a -> a -> Cbool
 (./=) :: a -> a -> Cbool
 (./=) x y = cnot (x .== y)

class Cord a where
 (.< ) :: a -> a -> Cbool
 (.<=) :: a -> a -> Cbool
 (.>=) :: a -> a -> Cbool
 (.> ) :: a -> a -> Cbool

lift2 :: (a -> b -> Bool) -> a -> b -> Cbool
lift2 f x y = if f x y then true else false

instance Eq a => Ceq a where
 (.==) = lift2 (==)
 (./=) = lift2 (/=)

instance Ord a => Cord a where
 (.< ) = lift2 (< )
 (.<=) = lift2 (<=)
 (.>=) = lift2 (>=)
 (.> ) = lift2 (> )

(.&&) :: Cbool -> Cbool -> Cbool
(.&&) f g = f g false

(.||) :: Cbool -> Cbool -> Cbool
(.||) f g = f true g

cnot :: Cbool -> Cbool
cnot f a b = f b a
