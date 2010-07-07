{-# LANGUAGE ExtendedDefaultRules #-}
module CFTests where

import Control.Applicative
import Data.List
import qualified Data.Set as S
import Math.ContinuedFraction
import Test.QuickCheck
import Test.Framework (testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

default (Integer, Rational)

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

tests = 
    [ testGroup "asCF"                  asCF_tests
    , testGroup "asGCF"                 asGCF_tests
    , testGroup "truncateCF"            truncateCF_tests
    , testGroup "partitionCF"           partitionCF_tests
    , testGroup "evenCF"                evenCF_tests
    , testGroup "oddCF"                 oddCF_tests
    , testGroup "equiv"                 equiv_tests
    , testGroup "setDenominators"       setDenominators_tests
    , testGroup "setNumerators"         setNumerators_tests
    , testGroup "convergents"           convergents_tests
    , testGroup "steed"                 steed_tests
    , testGroup "lentz"                 lentz_tests
    , testGroup "modifiedLentz"         modifiedLentz_tests
    , testGroup "sumPartialProducts"    sumPartialProducts_tests
    ]

asCF_tests =
    [ testProperty "preserves convergents" prop_asCF_preserves_convergents
    ]

prop_asCF_preserves_convergents orig = convergents orig == convergents new
    where
        new = uncurry cf (asCF orig)
        
asGCF_tests =
    [ testProperty "preserves convergents" prop_asCF_preserves_convergents
    ]

prop_asGCF_preserves_convergents orig = convergents orig == convergents new
    where
        new = uncurry gcf (asGCF orig)

truncateCF_tests = 
    [ testProperty "truncates convergents" prop_truncateCF_truncates_convergents
    ]

prop_truncateCF_truncates_convergents orig (NonNegative n) = convergents truncated `isPrefixOf` convergents orig
    where
        truncated = truncateCF n orig

prop_truncateCF_bounds_convergents orig (NonNegative n) = length (convergents truncated) <= n+1
    where
        truncated = truncateCF n orig

partitionCF_tests =
    [ testProperty "preserves convergents" prop_partitionCF_preserves_convergents
    ]

prop_partitionCF_preserves_convergents cf = 
    length (snd (asGCF cf)) > 1
    ==> (origConvergents == S.union evenConvergents oddConvergents)
    where
        origConvergents = S.fromList $ convergents cf
        evenConvergents = S.fromList $ convergents evenCF
        oddConvergents  = S.fromList $ convergents oddCF
        
        (evenCF, oddCF) = partitionCF cf

evenCF_tests = 
    [ testProperty "preserves last convergent" prop_evenCF_preserves_last_convergent
    ]

prop_evenCF_preserves_last_convergent orig = origResult == evenResult
    where
        origResult = last $ convergents orig
        evenResult = last $ convergents (evenCF orig)

oddCF_tests = 
    [ testProperty "preserves last convergent" prop_oddCF_preserves_last_convergent
    ]

prop_oddCF_preserves_last_convergent orig = origResult == oddResult
    where
        origResult = last $ convergents orig
        oddResult  = last $ convergents (oddCF orig)

equiv_tests =
    [ testProperty "preserves convergents" prop_equiv_preserves_convergents
    ]

prop_equiv_preserves_convergents cs orig = convergents orig == convergents new
    where
        new = equiv cs orig

setDenominators_tests =
    [ testProperty "preserves convergents" prop_setDenominators_preserves_convergents
    ]

prop_setDenominators_preserves_convergents denoms orig = convergents orig == convergents new
    where
        new = setDenominators denoms orig

setNumerators_tests =
    [ testProperty "preserves convergents" prop_setNumerators_preserves_convergents
    ]

prop_setNumerators_preserves_convergents nums orig = convergents orig == convergents new
    where
        new = setNumerators nums orig

convergents_tests =
    [ testProperty "not null" prop_convergents_not_null
    ]

prop_convergents_not_null = not . null . convergents

steed_tests =
    [ testProperty "not null" prop_steed_not_null
    ]

prop_steed_not_null = not . null . steed

lentz_tests =
    [ testProperty "not null" prop_lentz_not_null
    ]

prop_lentz_not_null = not . null . convergents

modifiedLentz_tests =
    [ testProperty "not null" prop_modifiedLentz_result_not_null
    , testProperty "sublists not null" prop_modifiedLentz_sublists_not_null
    ]

prop_modifiedLentz_sublists_not_null = not . any null . modifiedLentz 1e-30

prop_modifiedLentz_result_not_null = not . null . modifiedLentz 1e-30

sumPartialProducts_tests =
    [ testProperty "preserves partial sums" prop_sumPartialProducts_preserves_partial_sums
    ]

prop_sumPartialProducts_preserves_partial_sums xs = scanl (+) 0 (tail $ scanl (*) 1 xs) == convergents (sumPartialProducts xs)