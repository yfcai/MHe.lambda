-- simple type checker

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
cont1 = [(0,type0),(1,type1),(3,type3)] :: Context

-- tnormal calculates the normal form of type signatures
-- with type variables listed from left to right
tnormal :: Type -> Type
tnormal a = let (_,_,b) = loop 0 Map.empty a in b where
 loop :: Int -> Map.Map Int Int -> Type -> (Int, Map.Map Int Int, Type)
 loop xi f (Tcon  ) = (xi, f, Tcon)
 loop xi f (Tvar i) = case Map.insertLookupWithKey (const const) i xi f of
  (Nothing, g) -> (xi + 1, g, Tvar xi)
  (Just j , _) -> (xi    , f, Tvar j )
 loop xi f (a :> b) = let
  (pi, g, c) = loop xi f a
  (nu, h, d) = loop pi g b in (nu, h, c :> d)

-- alpha equivalence of types
-- normalise type first so that they can be compared trivially
instance Eq Type where
 (==) a b = eq (tnormal a) (tnormal b) where
  eq (Tcon  ) (Tcon  ) = True
  eq (Tvar i) (Tvar j) = i == j
  eq (a :> b) (c :> d) = eq a c && eq b d
  eq _        _        = False

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

class Typable a where
 sinfer :: a -> Maybe Type
 pinfer :: a -> Maybe Type

instance Typable Ilambda where
 sinfer = slinfer . i_to_l
 pinfer = plinfer . i_to_l

instance Typable Llambda where
 sinfer = slinfer
 pinfer = plinfer

-- whether Tvar j is free in the type b
is_free :: Int -> Type -> Bool
is_free j b = case b of
 Tcon   -> False
 Tvar i -> i == j
 c :> d -> is_free j c || is_free j d

-- substitute each occurrence of Tvar i with b in c
tsub :: Int -> Type -> Type -> Type
tsub i b c = case c of
 Tcon   -> c
 Tvar j -> if j == i then b else c
 d :> e -> tsub i b d :> tsub i b e

-- substitute each Tvar i of a with its value in tmap if exists
tsub_all :: Type -> Map.Map Int Type -> Type
tsub_all a tmap = case a of
 Tcon   -> a
 Tvar i -> Map.findWithDefault a i tmap
 b :> c -> tsub_all b tmap :> tsub_all c tmap

-- calculate the most-general-substitution of type-variables
-- from a set of constraints if it exists
mgs :: [Constraint] -> Maybe (Map.Map Int Type)
mgs cs = loop cs (Just Map.empty) where
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

-- BEGIN simple type inference according to PIERCE --
--- constraints of an entire term are generated in one walk
--- most-general-substitution is calculated thereupon
--- of the attributes
---- context is top-down
---- set of constraints is bottom-up
---- next-available-type-variable xi is leftmost-outermost

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

slinfer :: Llambda -> Maybe Type
slinfer term = let
 (a, cs) = lconstraints term
 in mgs cs >>= \tmap -> return (tnormal (tsub_all a tmap))

-- END simple type inference according to PIERCE --

-- BEGIN simple type inference according to WELLS --
--- each subterm generates a principal pair of (context, type) on its own
--- where principality means the least (by containment) set of terms
--- that have the type under the context
--- of the attributes
---- context is bottom-up
---- type is bottom-up
---- next-available-type-variable xi is leftmost-innermost
----- for it is generated by Tvar instead of Tabs

-- we enforce the discipline that each context is sorted in ascending order
type Context = [(Int, Type)]

-- make Type an instance of Ord so that we can use
-- default ordering on tuple
-- but types are not supposed to be compared
instance Ord Type where
 compare = error "Types are not supposed to be compared"

-- generate constraints from two contexts
-- taking inspiration from hackage data-ordlist-0.2
pconstraints :: Context -> Context -> [Constraint]
pconstraints [] _ = []
pconstraints _ [] = []
pconstraints aas@((i, a):as) bbs@((j, b):bs) = case compare i j of
 LT -> pconstraints as bbs
 GT -> pconstraints aas bs
 EQ -> Unify a b : pconstraints as bs

-- lookup the type of a term variable in context
-- computes also the context minus that term variable
context_lookup :: Int -> Context -> Maybe (Type, Context)
context_lookup i = loop where
 loop ((j,a):delta) = case compare j i of
  LT -> loop delta >>= \(b, gamma) -> return (b, (j,a):gamma)
  EQ -> return (a, delta)
  GT -> Nothing
 loop [] = Nothing

-- merge gamma and delta subject to substitution according to f
merge_contexts :: Map.Map Int Type -> Context -> Context -> Context
merge_contexts f = loop where
 mapf = map (\(i, a) -> (i, tsub_all a f))
 loop as [] = mapf as
 loop [] bs = mapf bs
 loop aas@((i,a):as) bbs@((j,b):bs) = case compare i j of
  LT -> (i, tsub_all a f) : loop as bbs
  GT -> (j, tsub_all b f) : loop aas bs
  EQ -> (i, tsub_all a f) : loop as bs

plinfer :: Llambda -> Maybe Type
plinfer t = loop (-1) 0 t >>= return . tnormal . (\(a,_,_) -> a) where
 loop :: Int -> Int -> Llambda -> Maybe (Type, Int, Context)
 loop depth xi (Lcon _  ) = return (Tcon, xi, [])
 loop depth xi (Lvar i  ) = return (Tvar xi, xi + 1, [(i, Tvar xi)])
 loop depth xi (Llam _ s) = let
  bind_level = depth + 1
  in loop bind_level xi s >>= \(a, pi, gamma) ->
     case context_lookup bind_level gamma of
      Nothing         -> return (Tvar pi :> a, pi + 1, gamma)
      Just (b, delta) -> return (b :> a, pi, delta)
 loop depth xi (Lapp s t) =
  loop depth xi s >>= \(a, pi, gamma) ->
  loop depth pi t >>= \(b, nu, delta) -> let c = Tvar nu in
   mgs (Unify a (b :> c) : pconstraints gamma delta) >>= \f ->
   return (tsub_all c f, nu + 1, merge_contexts f gamma delta)
-- END simple type inference according to WELLS --
