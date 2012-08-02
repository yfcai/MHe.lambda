-- polymorphic type checker for Ilambda

module TYP where

import LAM
import Char(ord, chr)
import qualified Data.Map as Map

infixr 5 :> -- same as :

data Type = Tcon | Tvar Int | Type :> Type deriving Eq

data Constraint = Unify Type Type

type1 = ((Tvar 0 :> Tcon):>Tvar 1):>Tvar 26
type2 = Tvar 2 :> Tvar 3
cons1 = Unify type1 type2

instance Show Type where
 show Tcon              = "*"
 show (Tvar i)          = let j = i - 26 in if j < 0
                          then chr (ord 'z' + 1 + j) : [] else show j
 show (a@(_ :> _) :> b) = '(' : show a ++ ") -> " ++ show b
 show (a :> b)          = show a ++ " -> " ++ show b

instance Show Constraint where
 show (Unify a b) = "\n " ++ show a ++ "  ==  " ++ show b

class Typable a where
 infer :: a -> Maybe Type

instance Typable Ilambda where
 infer = linfer . i_to_l

instance Typable Llambda where
 infer = linfer


lconstraints :: Llambda -> (Type, [Constraint])
lconstraints term = let (a,x,c) = loop (-1) Map.empty 0 term in (a,c) where
 -- computes (type-of-term, next-available-type-variable, constraints)
 -- from level-of-term context available-type-variable term
 loop :: Int -> (Map.Map Int Type) -> Int -> Llambda
                 -> (Type, Int, [Constraint])
 loop level gamma xi term = case term of
  Lcon _   -> (Tcon, xi, [])
  Lvar i   -> (Map.findWithDefault (error $ "Unbound variable at level "
               ++ show i ++" during constraint generation") i gamma
              , xi, [])
  Llam x s -> let (a,x,c) = loop (level + 1)
                   (Map.insert (level + 1) (Tvar xi) gamma) (xi + 1) s
              in (Tvar xi :> a, x, c)
  Lapp s t -> let (a,x,c) = loop level gamma (xi + 1) s
                  (b,y,d) = loop level gamma x        t
              in (Tvar xi, y, Unify (b :> Tvar xi) a : c ++ d)

linfer = error "yo"

