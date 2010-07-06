module CFTests where

import Control.Applicative
import Data.List
import qualified Data.Set as S
import Math.ContinuedFraction
import Test.QuickCheck

instance Arbitrary a => Arbitrary (CF a) where
    arbitrary = do
        mode <- arbitrary
        if mode
            then liftA2 cf arbitrary arbitrary
            else liftA2 gcf arbitrary arbitrary

instance (CoArbitrary a, Num a) => CoArbitrary (CF a) where
    coarbitrary cf = coarbitrary b0 . coarbitrary terms
        where
            (b0, terms) = asGCF cf

prop_asCF_preserves_convergents :: CF Rational -> Bool
prop_asCF_preserves_convergents orig = convergents orig == convergents new
    where
        new = uncurry cf (asCF orig)
        
prop_asGCF_preserves_convergents :: CF Rational -> Bool
prop_asGCF_preserves_convergents orig = convergents orig == convergents new
    where
        new = uncurry gcf (asGCF orig)

prop_truncateCF_truncates_convergents :: Fractional a => CF a -> NonNegative Int -> Bool
prop_truncateCF_truncates_convergents orig (NonNegative n) = convergents truncated `isPrefixOf` convergents orig
    where
        truncated = truncateCF n orig

prop_truncateCF_bounds_convergents :: Fractional a => CF a -> NonNegative Int -> Bool
prop_truncateCF_bounds_convergents orig (NonNegative n) = length (convergents truncated) <= n+1
    where
        truncated = truncateCF n orig

prop_partition_preserves_convergents :: CF Rational -> Property
prop_partition_preserves_convergents cf = 
    length (snd (asGCF cf)) > 1
    ==> (origConvergents == S.union evenConvergents oddConvergents)
    where
        origConvergents = S.fromList $ convergents cf
        evenConvergents = S.fromList $ convergents evenCF
        oddConvergents  = S.fromList $ convergents oddCF
        
        (evenCF, oddCF) = partitionCF cf

prop_equiv_preserves_convergents :: [Rational] -> CF Rational -> Bool
prop_equiv_preserves_convergents cs orig = convergents orig == convergents new
    where
        new = equiv cs orig

prop_setDenominators_preserves_convergents :: [Rational] -> CF Rational -> Bool
prop_setDenominators_preserves_convergents denoms orig = convergents orig == convergents new
    where
        new = setDenominators denoms orig

prop_setNumerators_preserves_convergents :: [Rational] -> CF Rational -> Bool
prop_setNumerators_preserves_convergents nums orig = convergents orig == convergents new
    where
        new = setNumerators nums orig

prop_convergents_not_null :: Fractional a => CF a -> Bool
prop_convergents_not_null = not . null . convergents

prop_steed_not_null :: Fractional a => CF a -> Bool
prop_steed_not_null = not . null . steed

prop_lentz_not_null :: Fractional a => CF a -> Bool
prop_lentz_not_null = not . null . convergents

prop_modifiedLentz_sublists_not_null :: Fractional a => CF a -> Bool
prop_modifiedLentz_sublists_not_null = not . any null . modifiedLentz 1e-30

prop_modifiedLentz_result_not_null :: Fractional a => CF a -> Bool
prop_modifiedLentz_result_not_null = not . null . modifiedLentz 1e-30

prop_sumPartialProducts_correct :: [Rational] -> Bool
prop_sumPartialProducts_correct xs = scanl (+) 0 (tail $ scanl (*) 1 xs) == convergents (sumPartialProducts xs)