-- a module for the integer cohomology structure of a K3 surface
module K3 (
	K3Domain,
	degK3,
	rangeK3,
	oneK3, xK3,
	cupLSparse,
	cupAdLSparse
	) where

import Data.Array
import Data.List
import Data.MemoTrie

-- type for indexing the cohomology base
type K3Domain = Int

rangeK3 = [0..23] :: [K3Domain]

oneK3 = 0 :: K3Domain
xK3 = 23 :: K3Domain

rangeK3Deg :: Int -> [K3Domain]
rangeK3Deg 0 = [0]
rangeK3Deg 2 = [1..22]
rangeK3Deg 4 = [23]
rangeK3Deg _ = []

delta i j = if i==j then 1 else 0

-- degree of the element of H^*(S), indexed by i
degK3 :: (Num d) => K3Domain -> d
degK3 0 = 0 
degK3 23 = 4
degK3 i = if i>0 && i < 23 then 2 else error "Not a K3 index"

-- the negative e8 intersection matrix
e8 = array ((1,1),(8,8)) $
	zip [(i,j) | i <- [1..8],j <-[1..8]] [
	-2, 1, 0, 0, 0, 0, 0, 0,
	1, -2, 1, 0, 0, 0, 0, 0,
	0, 1, -2, 1, 0, 0, 0, 0,
	0, 0, 1, -2, 1, 0, 0, 0,
	0, 0, 0, 1, -2, 1, 1, 0,
	0, 0, 0, 0, 1, -2, 0, 1,
	0, 0, 0, 0, 1, 0, -2, 0,
	0, 0, 0, 0, 0, 1, 0, -2 :: Int]

-- the inverse matrix of e8
inve8 = array ((1,1),(8,8)) $
	zip [(i,j) | i <- [1..8],j <-[1..8]] [
	-2, -3, -4, -5, -6, -4, -3, -2, 
	-3, -6, -8,-10,-12, -8, -6, -4,
	-4, -8,-12,-15,-18,-12, -9, -6, 
	-5,-10,-15,-20,-24,-16,-12, -8,
	-6,-12,-18,-24,-30,-20,-15,-10,
	-4, -8,-12,-16,-20,-14,-10, -7, 
	-3, -6, -9,-12,-15,-10, -8, -5, 
	-2, -4, -6, -8,-10, -7, -5, -4 :: Int]

-- hyperbolic lattice
u 1 2 = 1
u 2 1 = 1
u 1 1 = 0
u 2 2 = 0
u i j = undefined

-- cup product pairing for K3 cohomology
bilK3 :: K3Domain -> K3Domain -> Int
bilK3 ii jj = let 
	(i,j) = (min ii jj, max ii jj) 
	in
	if (i < 0) || (j > 23) then undefined else
	if (i == 0) then delta j 23 else
	if (i >= 1) && (j <= 2) then u i j else
	if (i >= 3) && (j <= 4) then u (i-2) (j-2) else
	if (i >= 5) && (j <= 6) then u (i-4) (j-4) else
	if (i >= 7) && (j <= 14) then e8 ! ((i-6), (j-6)) else
	if (i >= 15) && (j<= 22) then e8 ! ((i-14), (j-14))  else
	0

-- inverse matrix to cup product pairing
bilK3inv :: K3Domain -> K3Domain -> Int
bilK3inv ii jj = let 
	(i,j) = (min ii jj, max ii jj) 
	in
	if (i < 0) || (j > 23) then undefined else
	if (i == 0) then delta j 23 else
	if (i >= 1) && (j <= 2) then u i j else
	if (i >= 3) && (j <= 4) then u (i-2) (j-2) else
	if (i >= 5) && (j <= 6) then u (i-4) (j-4) else
	if (i >= 7) && (j <= 14) then inve8 ! ((i-6), (j-6)) else
	if (i >= 15) && (j<= 22) then inve8 ! ((i-14), (j-14))  else
	0 

-- cup product with two factors
-- a_i * a_j = sum [cup k (i,j) * a_k | k<- rangeK3]
cup :: K3Domain -> (K3Domain,K3Domain) -> Int
cup = memo2 r where
	r k (0,i) = delta k i
	r k (i,0) = delta k i
	r _ (i,23) = 0
	r _ (23,i) = 0
	r 23 (i,j) =  bilK3 i j
	r _ _ = 0

-- indices where the cup product does not vanish
cupNonZeros :: [ (K3Domain,(K3Domain,K3Domain)) ]
cupNonZeros = [ (k,(i,j)) | i<-rangeK3, j<-rangeK3, k<-rangeK3, cup k (i,j) /= 0]

-- cup product of a list of factors
cupLSparse :: [K3Domain] -> [(K3Domain,Int)]
cupLSparse = cu . filter (/=oneK3) where
	cu [] = [(oneK3,1)]; cu [i] = [(i,1)]
	cu [i,j] = [(k,z) | k<-rangeK3, let z = cup k (i,j), z/=0]
	cu _ = []

-- comultiplication, adjoint to the cup product
-- Del a_k = sum [cupAd (i,j) k * a_i `tensor` a_k | i<-rangeK3, j<-rangeK3]
cupAd :: (K3Domain,K3Domain) -> K3Domain -> Int
cupAd = memo2 ad where 
	ad (i,j) k = negate $ sum [bilK3inv i ii * bilK3inv j jj 
		* cup kk (ii,jj) * bilK3 kk k |(kk,(ii,jj)) <- cupNonZeros ]

-- n-fold comultiplication
cupAdLSparse :: Int -> K3Domain -> [([K3Domain],Int)]
cupAdLSparse = memo2 cals where
	cals 0 k = if k == xK3 then [([],1)] else []
	cals 1 k = [([k], 1)]
	cals 2 k = [([i,j],ca) | i<-rangeK3, j<-rangeK3, let ca = cupAd (i,j) k, ca /=0]
	cals n k = clean [(i:r,v*w) |([i,j],w)<-cupAdLSparse 2 k, (r,v)<-cupAdLSparse(n-1) j]
	clean = map (\g -> (fst$head g, sum$(map snd g))). groupBy cg.sortBy cs  
	cs = (.fst).compare.fst; cg = (.fst).(==).fst

