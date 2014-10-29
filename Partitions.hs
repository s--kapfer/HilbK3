{-# LANGUAGE TypeOperators, TypeFamilies #-}

-- implements data structure and basic functions for partitions
module Partitions where

import Data.Permute
import Data.Maybe
import qualified Data.List 
import Data.MemoTrie

class (Eq a, HasTrie a) => Partition a where
	-- length of a partition
	partLength :: Integral i => a -> i 
	
	-- weight of a partition
	partWeight :: Integral i => a -> i
	
	-- degree of a partition = weight - length
	partDegree :: Integral i => a -> i
	partDegree p = partWeight p - partLength p
	
	-- the z, occuring in all papers
	partZ :: Integral i => a -> i
	partZ = partZ.partAsAlpha
	
	-- conjugated partition
	partConj :: a -> a
	partConj = res. partAsAlpha where
		make l (m:r) = l : make (l-m) r
		make _ [] = []
		res (PartAlpha r) = partFromLambda $ PartLambda $ make (sum r) r
	
	-- empty partition
	partEmpty :: a
	
	-- transformation to alpha-notation
	partAsAlpha :: a -> PartitionAlpha
	-- transformation from alpha-notation
	partFromAlpha :: PartitionAlpha -> a
	-- transformation to lambda-notation
	partAsLambda :: a -> PartitionLambda Int
	-- transformation from lambda-notation
	partFromLambda :: (Integral i, HasTrie i) => PartitionLambda i -> a
	
	-- all permutationens of a certain cycle type
	partAllPerms :: a -> [Permute]
	
-----------------------------------------------------------------------------------------

-- data type for partitiones in alpha-notation
-- (list of multiplicities)
newtype PartitionAlpha = PartAlpha { alphList::[Int] }

-- reimplementation of the zipWith function
zipAlpha op (PartAlpha a) (PartAlpha b) = PartAlpha $ z a b where
	z (x:a) (y:b) = op x y : z a b
	z [] (y:b) = op 0 y : z [] b
	z (x:a) [] = op x 0 : z a []
	z [] [] = []

-- reimplementation of the (:) operator
alphaPrepend 0 (PartAlpha []) = partEmpty
alphaPrepend i (PartAlpha  r) = PartAlpha (i:r)

-- all partitions of a given weight
partOfWeight :: Int -> [PartitionAlpha]
partOfWeight = let
	build n 1 acc = [alphaPrepend n acc]
	build n c acc = concat [ build (n-i*c) (c-1) (alphaPrepend i acc) | i<-[0..div n c]] 
	a 0 = [PartAlpha []]
	a w =  if w<0 then [] else  build w w partEmpty
	in memo a

-- all partitions of given weight and length
partOfWeightLength = let
	build 0 0 _ = [partEmpty]
	build w 0 _ = []
	build w l c = if l > w || c>w then [] else
		concat [ map (alphaPrepend i) $ build (w-i*c) (l-i) (c+1) 
			| i <- [0..min l $ div w c]]
	a w l = if w<0 || l<0 then [] else build w l 1
	in memo2 a

-- determines the cycle type of a permutation
cycleType :: Permute -> PartitionAlpha
cycleType p = let 
	lengths = Data.List.sort $ map Data.List.length $ cycles p
	count i 0 [] = partEmpty
	count i m [] = PartAlpha [m]
	count i m (x:r) = if x==i then count i (m+1) r 
		else alphaPrepend m (count (i+1) 0 (x:r)) 
	in count 1 0 lengths

-- constructs a permutation from a partition
partPermute :: Partition a => a -> Permute
partPermute = let
	make l n acc (PartAlpha x) = f x where
		f [] = cyclesPermute n acc 
		f (0:r) = make (l+1) n acc $ PartAlpha r
		f (i:r) = make l (n+l) ([n..n+l-1]:acc) $ PartAlpha ((i-1):r)
	in make 1 0 [] . partAsAlpha

instance Partition PartitionAlpha where
	partWeight (PartAlpha r) = fromIntegral $ sum $ zipWith (*) r [1..]
	partLength (PartAlpha r) = fromIntegral $ sum r
	partEmpty = PartAlpha []
	partZ (PartAlpha l) = foldr (*) 1 $ 
		zipWith (\a i-> factorial a*i^a) (map fromIntegral l) [1..] where
			factorial n = if n==0 then 1 else n*factorial(n-1)
	partAsAlpha = id
	partFromAlpha = id
	partAsLambda (PartAlpha l) = PartLambda $ reverse $ f 1 l where
		f i [] = []
		f i (0:r) = f (i+1) r
		f i (m:r) = i : f i ((m-1):r)
	partFromLambda = lambdaToAlpha
	partAllPerms = partAllPerms . partAsLambda

instance Eq PartitionAlpha where
	PartAlpha p == PartAlpha q = findEq p q where
		findEq [] [] = True
		findEq (a:p) (b:q) = (a==b) && findEq p q
		findEq [] q = isZero q
		findEq p [] = isZero p 
		isZero = all (==0) 

instance Ord PartitionAlpha where
	compare a1 a2 = compare (partAsLambda a1) (partAsLambda a2)

instance Show PartitionAlpha where 
	show p = let
		leftBracket = "(|"  
		rightBracket = "|)" 
		rest [] = rightBracket
		rest [i] = show i ++ rightBracket
		rest (i:q) = show i ++ "," ++ rest q
		in leftBracket ++ rest (alphList p) 

instance HasTrie PartitionAlpha where
	newtype PartitionAlpha :->: a =  TrieType { unTrieType :: [Int] :->: a }
	trie f = TrieType $ trie $ f . PartAlpha
	untrie f =  untrie (unTrieType f) . alphList
	enumerate f  = map (\(a,b) -> (PartAlpha a,b)) $ enumerate (unTrieType f)

-----------------------------------------------------------------------------------------

-- data type for partitions in lambda-notation
-- (descending list of positive numbers)
newtype PartitionLambda i = PartLambda { lamList :: [i] }

lambdaToAlpha :: Integral i => PartitionLambda i -> PartitionAlpha
lambdaToAlpha (PartLambda []) = PartAlpha[] 
lambdaToAlpha (PartLambda (s:p)) = lta 1 s p [] where
	lta _ 0 _ a = PartAlpha a
	lta m c [] a = lta 0 (c-1) [] (m:a)
	lta m c (s:p) a = if c==s then lta (m+1) c p a else 
		lta 0 (c-1) (s:p) (m:a)

instance (Integral i, HasTrie i) => Partition (PartitionLambda i) where
	partWeight (PartLambda r) = fromIntegral $ sum r
	partLength (PartLambda r) = fromIntegral $ length r
	partEmpty = PartLambda []
	partAsAlpha = lambdaToAlpha
	partAsLambda (PartLambda r) = PartLambda $ map fromIntegral r
	partFromAlpha (PartAlpha l) = PartLambda $ reverse $ f 1 l where
		f i [] = []
		f i (0:r) = f (i+1) r
		f i (m:r) = i : f i ((m-1):r)
	partFromLambda (PartLambda r) = PartLambda $ map fromIntegral r
	partAllPerms (PartLambda l) = it $ Just $ permute $ partWeight $ PartLambda l where
		it (Just p) = if Data.List.sort (map length $ cycles p) == r 
			then p : it (next p) else it (next p)
		it Nothing = []
		r = map fromIntegral $ reverse l

instance (Eq i, Num i) => Eq (PartitionLambda i) where
	PartLambda p == PartLambda q = findEq p q where
		findEq [] [] = True
		findEq (a:p) (b:q) = (a==b) && findEq p q
		findEq [] q = isZero q
		findEq p [] = isZero p 
		isZero = all (==0) 

instance (Ord i, Num i) => Ord (PartitionLambda i) where
	compare p1 p2 = if weighteq == EQ then compare l1 l2 else weighteq where
		(PartLambda l1, PartLambda l2) = (p1, p2)
		weighteq = compare (sum l1) (sum l2)

instance (Show i) => Show (PartitionLambda i) where
	show (PartLambda p) = "[" ++ s ++ "]" where
		s = concat $ Data.List.intersperse "-" $ map show p

instance HasTrie i => HasTrie (PartitionLambda i) where
	newtype (PartitionLambda i) :->: a =  TrieTypeL { unTrieTypeL :: [i] :->: a }
	trie f = TrieTypeL $ trie $ f . PartLambda
	untrie f =  untrie (unTrieTypeL f) . lamList
	enumerate f  = map (\(a,b) -> (PartLambda a,b)) $ enumerate (unTrieTypeL f)

