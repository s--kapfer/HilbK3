-- A module implementing base change matrices for symmetric functions
module SymmetricFunctions(
	monomialPower,
	powerMonomial,
	factorial
	) where

import Data.List 
import Data.MemoTrie
import Data.Ratio
import Partitions

-- binomial coefficients
choose n k = ch1 n k where
	ch1 = memo2 ch
	ch 0 0 = 1
	ch n k = if n<0 || k<0 then 0 else if k> div n 2 + 1 then ch1 n (n-k) else
		ch1(n-1) k + ch1 (n-1) (k-1)

-- multinomial coefficients
multinomial 0 [] = 1
multinomial n [] = 0
multinomial n (k:r) = choose n k * multinomial (n-k) r

-- factorial function
factorial 0 = 1
factorial n = n*factorial(n-1)

-- http://www.mat.univie.ac.at/~slc/wpapers/s68vortrag/ALCoursSf2.pdf , p. 48
-- scalar product between monomial symmetric functions and power sums
monomialScalarPower moI poI = (s * partZ poI) `div` quo where
	mI = partAsAlpha moI
	s = sum[a* moebius b | (a,b)<-finerPart mI (partAsLambda poI)]
	quo = product[factorial i| let PartAlpha l =mI, i<-l] 
	nUnder 0 [] = [[]]
	nUnder n [] = [] 
	nUnder n (r:profile) = concat[map (i:) $ nUnder (n-i) profile | i<-[0..min n r]]
	finerPart (PartAlpha a) (PartLambda l) = nub [(a`div` sym sb,sb) | (a,b)<-fp 1 a l, let sb = sort b] where
		sym = s 0 []
		s n acc [] = factorial n
		s n acc (a:o) = if a==acc then s (n+1) acc o else factorial n * s 1 a o
		fp i [] l = if all (==0) l then [(1,[[]|x<-l])] else []
		fp i (0:ar) l = fp (i+1) ar l
		fp i (m:ar) l = [(v*multinomial m p,addprof p op) 
			| p <- nUnder m (map (flip div i) l), 
			(v,op) <- fp (i+1) ar (zipWith (\j mm -> j-mm*i) l p)] where
				addprof = zipWith (\mm l -> replicate mm i ++ l)
	moebius l = product [(-1)^c * factorial c | m<-l, let c = length m - 1]

-- base change matrix from monomials to power sums
-- no integer coefficients
-- m_j = sum [ p_i * powerMonomial i j | i<-partitions]
powerMonomial :: (Partition a, Partition b) => a->b->Ratio Int
powerMonomial poI moI = monomialScalarPower moI poI % partZ poI

-- base change matrix from power sums to monomials
-- p_j = sum [m_i * monomialPower i j | i<-partitions]
monomialPower :: (Partition a, Partition b, Num i) => a->b->i 
monomialPower lambda mu = fromIntegral $ numerator $ 
	memoizedMonomialPower (partAsLambda lambda) (partAsLambda mu)  
memoizedMonomialPower = memo2 mmp1 where
	mmp1 l m  = if partWeight l == partWeight m then mmp2 (partWeight m) l m else 0 
	mmp2 w l m = invertLowerDiag (map partAsLambda $ partOfWeight w) powerMonomial l m

-- inversion of lower triangular matrix
invertLowerDiag vs a = ild where
	ild = memo2 inv
	delta i j = if i==j then 1 else 0
	inv i j | i<j = 0
		| otherwise = (delta i j - sum [a i k * ild k j | k<-vs, i>k , k>= j]) / a i i