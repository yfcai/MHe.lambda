-- polymorphic type checker for Ilambda

module TYP where

import LAM
import Char(ord, chr)
import qualified Data.Map as Map

infixr 5 :> -- same fixity as :

data Type = Tcon | Tvar Int | Type :> Type

data Constraint = Unify Type Type

type0 = Tvar 2 :> Tvar 3
type1 = ((Tvar 0 :> Tcon):>Tvar 1):>Tvar 26
type2 = ((Tvar 2 :> Tcon):>Tvar 1):>Tvar 0
type3 = ((Tvar 0 :> Tcon):>Tvar 0):>Tvar 2
cons1 = Unify type1 type2

-- alpha equivalence of types
instance Eq Type where
 (==) a b = Nothing /= loop a b (Map.empty, Map.empty) where
  -- loop a b (empty, empty) == Just (f, f') iff f(a) == b and f'(b) == a
  loop :: Type -> Type -> (Map.Map Int Int, Map.Map Int Int)
       -> Maybe (Map.Map Int Int, Map.Map Int Int)
  loop (Tcon  ) (Tcon  ) maps   = return maps
  loop (a :> b) (c :> d) maps   = loop a c maps >>= loop b d
  loop (Tvar i) (Tvar j) (f,f') = let
   -- const const i j k = j
   (nothing, g ) = Map.insertLookupWithKey' (const const) i j f
   (nothin', g') = Map.insertLookupWithKey' (const const) j i f'
   check mb i = case mb of Nothing -> return (g, g')
                           Just k  -> if k == i then return (g, g') else Nothing
   in check nothing j >> check nothin' i
  loop _ _ _ = Nothing

instance Show Type where
 show a = let
  show_var i = let j = i - 26 in if j < 0
               then chr (ord 'z' + 1 + j) : [] else show j
  in case a of
  Tcon            -> "*"
  Tvar i          -> show_var i
  a@(_ :> _) :> b -> '(' : show a ++ ") -> " ++ show b
  a :> b          -> show a ++ " -> " ++ show b

instance Show Constraint where
 show (Unify a b) = "\n " ++ show a ++ "  ==  " ++ show b

class Stypable a where
 sinfer :: a -> Maybe Type

instance Stypable Ilambda where
 sinfer = slinfer . i_to_l

instance Stypable Llambda where
 sinfer = slinfer


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

is_free :: Int -> Type -> Bool
is_free a b = case b of
 Tcon   -> False
 Tvar i -> i == a
 c :> d -> is_free a c || is_free a d

-- substitute each occurrence of Tvar i with b in c
tsub :: Int -> Type -> Type -> Type
tsub i b c = case c of
 Tcon   -> c
 Tvar j -> if j == i then b else c
 d :> e -> tsub i b d :> tsub i b e

-- substitute each Tvar i of a with its value in tmap if exists
tsub_all a tmap = case a of
 Tcon   -> a
 Tvar i -> Map.findWithDefault a i tmap
 b :> c -> tsub_all b tmap :> tsub_all c tmap

sunify :: [Constraint] -> Maybe (Map.Map Int Type)
sunify cs = loop cs (Just Map.empty) where
 loop [] ss = ss
 loop (Unify a b : cs) ss = ss >>= \tmap -> case (a,b) of
  (Tvar i,_)  -> if is_free i b
                 then Nothing
                 else loop (uclean i b cs) (tclean i b tmap)
  (_,Tvar j)  -> if is_free j a
                 then Nothing
                 else loop (uclean j a cs) (tclean j a tmap)
  (c:>d,e:>f) -> loop (Unify c e : Unify d f : cs) ss
  otherwise   -> Nothing
 uclean i b = map (\(Unify c d) -> Unify (tsub i b c) (tsub i b d))
 tclean i b m = Just (Map.insert i b (Map.map (\c -> tsub i b c) m))

slinfer :: Llambda -> Maybe Type
slinfer term = let
 (a, cs) = lconstraints term
 in sunify cs >>= \tmap -> return (tsub_all a tmap)

