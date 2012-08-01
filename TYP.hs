-- polymorphic type checker for Ilambda

module TYP where

import LAM
import Char(ord, chr)
import qualified Data.Map as Map

infixr 5 :> -- same as :
data Type = Tcon | Tvar Int | Type :> Type deriving Eq

type1 = ((Tvar 97 :> Tcon):>Tvar 97):>Tvar 98

instance Show Type where
 show Tcon              = "*"
 show (Tvar i)          = chr i : []
 show (a@(_ :> _) :> b) = '(' : show a ++ ") -> " ++ show b
 show (a :> b)          = show a ++ " -> " ++ show b

class Typable a where
 infer :: a -> Maybe Type

instance Typable Ilambda where
 infer = linfer . i_to_l

instance Typable Llambda where
 infer = linfer

-- substitute the type-var designated by i with a in b
type_subst :: Int -> Type -> Type -> Type
type_subst i a b = loop b where
 loop Tcon     = Tcon
 loop (Tvar j) = if i == j then a else Tvar j
 loop (c :> d) = loop c :> loop d

-- infer the type of a term in de-Bruijn-levels notation
-- and report Nothing if the term is not well-typed
linfer :: Llambda -> Maybe Type
linfer s = error "ouch"

-- without type declaration, type system is forced to be polymorphic!
-- there is no way out!
