--packages: containers
{-# OPTIONS -fglasgow-exts -fno-monomorphism-restriction #-}
{-# LANGUAGE GADTs, UndecidableInstances, FlexibleInstances, EmptyDataDecls, Rank2Types, MultiParamTypeClasses, FunctionalDependencies, KindSignatures, OverlappingInstances,PatternSignatures,ScopedTypeVariables #-}
module HAppS.Data.IxSetTyped where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Monoid 

-- usage:
data Record = R {field1 :: Int, field2 :: String, field3 :: Bool } deriving (Eq,Ord,Read,Show)
instance Indexable Record Int where
    index = field1
instance Indexable Record String where
    index = field2
instance Indexable Record Bool where
    index = field3
type Ixs1 = (Cons String (Cons Bool Nil))
type Ixs2 = Cons Int Ixs1

foo = empty
bar :: List Index Ixs2 Record
bar = empty
{-
*Main> :t getOrd EQ (5::Int) foo

<interactive>:1:0:                                                                                                                                           
    No instance for (Get Nil Int)
      arising from a use of `getOrd' at <interactive>:1:0-21
    Possible fix: add an instance declaration for (Get Nil Int)
*Main> :t getOrd EQ (5::Int) bar
getOrd EQ (5::Int) bar :: List Index Ixs2 Record
-}

data Cons a b
data Nil
-- m parameter of List will always been Index, it's there only because i was experimenting with further generalizations
data List :: (* -> * -> *) -> * -> * -> * where
     Nil :: List m Nil x
     Cons :: m a x -> List m b x -> List m (Cons a b) x
data Index :: * -> * -> * where
     Ix :: Indexable x a => Map.Map a (Set.Set x) -> Index a x
unIx :: Index t t1 -> Map.Map t (Set.Set t1)
unIx (Ix m) = m
addIndex :: Indexable x a => List Index l x -> List Index (Cons a l) x
addIndex = Cons (Ix (Map.empty))

class Empty l x where
    empty :: List Index l x
instance Empty Nil x where
    empty = Nil
instance (Indexable x a, Empty b x) => Empty (Cons a b) x where
    empty = addIndex empty

class Update l a where
    update :: (m a x -> m a x) -> List m l x -> List m l x
instance Update (Cons a b) a where
    update f (Cons m xs) = Cons (f m) xs
instance (Update b a) => Update (Cons c b) a where
    update f (Cons m xs) = Cons m (update f xs)

class Get l a where
    get :: List m l x -> m a x
instance Get (Cons a b) a where
    get (Cons i _) = i
instance Get b a => Get (Cons c b) a where
    get (Cons _ xs) = get xs


class (Ord a, Ord b) => Indexable a b where
    index :: a -> b



getOrd :: (Ord k, Get l k) => Ordering -> k -> List Index l a -> List Index l a
getOrd ord k list = 
    let (Ix index) = get list
        (lt',eq',gt') = Map.splitLookup k index
        lt = concat $ map (Set.toList . snd) $ Map.toList lt'
        gt = concat $ map (Set.toList . snd) $ Map.toList gt'
        eq = maybe [] Set.toList eq'
    in foldr insert (empty' list) $
       case ord of
         LT -> lt
         GT -> gt
         EQ -> eq

empty' :: List Index l a -> List Index l a
empty' l = map' aux l
    where 
      aux :: Index a x -> Index a x
      aux (Ix _) = Ix Map.empty

orderBy list = Map.toList . unIx $ get list
map' :: (forall k. Index k a -> Index k a) -> List Index l a -> List Index l a
map' f Nil = Nil
map' f (Cons i xs) = Cons (f i) (map' f xs)
type IndexOp a = forall k. a -> Index k a -> Index k a
change :: IndexOp a -> a -> List Index l a -> List Index l a
change op a = map' (op a)

insert a = change insert' a
insert' :: b -> Index a b -> Index a b 
insert' v (Ix m) = Ix $ insert_ (index v) v m
insert_ :: (Ord a, Ord k) => k -> a -> Map.Map k (Set.Set a) -> Map.Map k (Set.Set a)
insert_ k v index = Map.insertWith Set.union k (Set.singleton v) index
delete a = change delete' a
delete' v (Ix m) = Ix $ delete_ (index v) v m
delete_ :: (Ord a, Ord k) => k -> a -> Map.Map k (Set.Set a) -> Map.Map k (Set.Set a)
delete_ k v index = Map.update remove k index
    where
    remove set = let set' = Set.delete v set
                 in if Set.null set' then Nothing else Just set' 
updateIx i new ixset = insert new $
                     maybe ixset (flip delete ixset) $
                     getOne $ ixset @= i

toSet :: List Index t x -> Set.Set x
toSet Nil = Set.empty
toSet (Cons (Ix m) _) = Map.fold Set.union Set.empty m
toList x = Set.toList $ toSet x
fromSet set = Set.fold insert empty set
size x = Set.size $ toSet x
union x1 x2 = fromSet $ Set.union (toSet x1) (toSet x2)
intersection x1 x2 = fromSet $ Set.intersection (toSet x1) (toSet x2)

getOne ixset = case toList ixset of
                   [x] -> Just x
                   _   -> Nothing
getOneOr def = fromMaybe def . getOne

ix @= v = getEQ v ix
ix @< v = getLT v ix
ix @> v = getGT v ix
ix @<= v = getLTE v ix
ix @>= v = getGTE v ix

ix @>< (v1,v2) = getLT v2 $ getGT v1 ix
ix @>=< (v1,v2) = getLT v2 $ getGTE v1 ix
ix @><= (v1,v2) = getLTE v2 $ getGT v1 ix
ix @>=<= (v1,v2) = getLTE v2 $ getGTE v1 ix

ix @+ list = foldr union (empty' ix) $ map (ix @=) list
ix @* list = foldr intersection (empty' ix) $ map (ix @=) list

getEQ :: (Get l k, Ord k) => k -> List Index l a -> List Index l a
getEQ v ix = getOrd EQ v ix


getLT v ix = getOrd LT v ix


getGT v ix = getOrd GT v ix


getLTE v ix = let ix2 = (getOrd LT v ix) in
                  maybe ix2 (flip insert ix2) $ getOne $ getEQ v ix


getGTE v ix = let ix2 = (getOrd GT v ix) in
                  maybe ix2 (flip insert ix2) $ getOne $ getEQ v ix


getRange k1 k2 ixset = intersection (getGTE k1 ixset) (getLT k2 ixset)

instance (Empty l x,Ord x) => Monoid (List Index l x) where
    mempty=empty
    mappend = union
