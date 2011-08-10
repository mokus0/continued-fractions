{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Safe #-}
#endif
module Math.ContinuedFraction
    ( CF
    , cf, gcf
    , asCF, asGCF
    
    , truncateCF
    
    , equiv
    , setNumerators
    , setDenominators
    
    , partitionCF
    , evenCF
    , oddCF
    
    , convergents
    , steed
    , lentz, lentzWith
    , modifiedLentz, modifiedLentzWith
    
    , sumPartialProducts
    ) where

import Control.Arrow ((***))
import Data.List (tails, mapAccumL)

-- * The 'CF' type and basic operations

-- I think I would like to try refactoring this stuff at some point to use
-- an "Inductive" CF type, something like:
-- 
-- > data CF a
-- >     = CFZero               -- eval CFZero          = 0
-- >     | CFAdd    a (CF a)    -- eval (CFAdd    b x) =      b + eval x
-- >     | CFCont a a (CF a)    -- eval (CFCont a b x) = a / (b + eval x)
-- 
-- Or perhaps Bill Gosper's "∞-centered" representation:
-- 
-- > data CF a
-- >     = CFInfinity           -- eval CFInfinity     = ∞
-- >     | CFCont a a (CF a)    -- eval (CFCont p q x) = p + q / eval x
-- 

-- |A continued fraction.  Constructed by 'cf' or 'gcf'.
data CF a 
    = CF a [a]
    -- ^ Not exported. See 'cf', the public constructor.
    | GCF a [(a,a)]
    -- ^ Not exported. See 'gcf', the public constructor.

-- |Construct a continued fraction from its first term and the 
-- partial denominators in its canonical form, which is the form 
-- where all the partial numerators are 1.
-- 
-- @cf a [b,c,d]@ corresponds to @a + (b \/ (1 + (c \/ (1 + d))))@,
-- or to @GCF a [(1,b),(1,c),(1,d)]@.
cf :: a -> [a] -> CF a
cf = CF

-- |Construct a continued fraction from its first term, its partial 
-- numerators and its partial denominators.
--
-- @gcf b0 [(a1,b1), (a2,b2), (a3,b3)]@ corresponds to
-- @b0 + (a1 \/ (b1 + (a2 \/ (b2 + (a3 \/ b3)))))@
gcf :: a -> [(a,a)] -> CF a
gcf = GCF

instance Show a => Show (CF a) where
    showsPrec p (CF b0 ab) = showParen (p>10)
        ( showString "cf "
        . showsPrec 11 b0
        . showChar ' '
        . showsPrec 11 ab
        )
    showsPrec p (GCF b0 ab) = showParen (p>10)
        ( showString "gcf "
        . showsPrec 11 b0
        . showChar ' '
        . showsPrec 11 ab
        )

instance Functor CF where
    fmap f (CF  b0 cf)  = CF  (f b0) (map f cf)
    fmap f (GCF b0 gcf) = GCF (f b0) (map (f *** f) gcf)

-- |Extract the partial denominators of a 'CF', normalizing it if necessary so 
-- that all the partial numerators are 1.
asCF  :: Fractional a => CF a -> (a, [a])
asCF (CF  b0 cf) = (b0, cf)
asCF (GCF b0 []) = (b0, [])
asCF (GCF b0 cf) = (b0, zipWith (*) bs cs)
    where
        (a:as, bs) = unzip cf
        cs = recip a : [recip (a*c) | c <- cs | a <- as]

-- |Extract all the partial numerators and partial denominators of a 'CF'.
asGCF :: Num a => CF a -> (a,[(a,a)])
asGCF (CF  b0  cf) = (b0, [(1, b) | b <- cf])
asGCF (GCF b0 gcf) = (b0, takeWhile ((/=0).fst) gcf)

-- |Truncate a 'CF' to the specified number of partial numerators and denominators.
truncateCF :: Int -> CF a -> CF a
truncateCF n (CF  b0 ab) = CF  b0 (take n ab)
truncateCF n (GCF b0 ab) = GCF b0 (take n ab)

-- |Apply an equivalence transformation, multiplying each partial denominator 
-- with the corresponding element of the supplied list and transforming 
-- subsequent partial numerators and denominators as necessary.  If the list
-- is too short, the rest of the 'CF' will be unscaled.
equiv :: Num a => [a] -> CF a -> CF a
equiv cs orig
    = gcf b0 (zip as' bs')
    where
        (b0, terms) = asGCF orig
        (as,bs) = unzip terms
        
        as' = zipWith (*) (zipWith (*) cs' (1:cs')) as
        bs' = zipWith (*) cs' bs
        cs' = cs ++ repeat 1

-- |Apply an equivalence transformation that sets the partial denominators 
-- of a 'CF' to the specfied values.  If the input list is too short, the 
-- rest of the 'CF' will be unscaled.
setDenominators :: Fractional a => [a] -> CF a -> CF a
setDenominators denoms orig
    = gcf b0 (zip as' bs')
    where
        (b0, terms) = asGCF orig
        (as,bs) = unzip terms
        
        as' = zipWith (*) as (zipWith (*) cs (1:cs))
        bs' = zipWith ($) (map const denoms ++ repeat id) bs
        cs = zipWith (/) bs' bs

-- |Apply an equivalence transformation that sets the partial numerators 
-- of a 'CF' to the specfied values.  If the input list is too short, the 
-- rest of the 'CF' will be unscaled.
setNumerators :: Fractional a => [a] -> CF a -> CF a
setNumerators numers orig
    = gcf b0 (zip as' bs')
    where
        (b0, terms) = asGCF orig
        (as,bs) = unzip terms
        
        as' = zipWith ($) (map const numers ++ repeat id) as
        bs' = zipWith (*) bs cs
        cs = zipWith (/) as' (zipWith (*) as (1:cs))

-- |Computes the even and odd parts, respectively, of a 'CF'.  These are new
-- 'CF's that have the even-indexed and odd-indexed convergents of the 
-- original, respectively.
partitionCF :: Fractional a => CF a -> (CF a, CF a)
partitionCF orig = case terms of
    []          -> (orig, orig)
    [(a1,b1)]   -> 
        let final = cf (b0 + a1/b1) []
         in (final, final)
    _           -> (evenPart, oddPart)
    where
        (b0, terms) = asGCF orig
        (as, bs)    = unzip terms
        
        pairs (a:b:rest) = (a,b) : pairs rest
        pairs [a] = [(a,0)]
        pairs _ = []
        
        alphas@(alpha1:alpha2:_) = zipWith (/) as (zipWith (*) bs (1:bs))
        
        evenPart = gcf b0 (zip cs ds)
            where
                cs =     alpha1 : [(-aOdd) * aEven  | (aEven, aOdd)  <- pairs (tail alphas)]
                ds = 1 + alpha2 : [1 + aOdd + aEven | (aOdd,  aEven) <- tail (pairs alphas)]
        
        oddPart = gcf (b0+alpha1) (zip cs ds)
            where
                cs = [(-aOdd) * aEven  | (aOdd, aEven) <- pairs alphas]
                ds = [1 + aOdd + aEven | (aEven, aOdd) <- pairs (tail alphas)]

-- |Computes the even part of a 'CF' (that is, a new 'CF' whose convergents are
-- the even-indexed convergents of the original).
evenCF :: Fractional a => CF a -> CF a
evenCF = fst . partitionCF

-- |Computes the odd part of a 'CF' (that is, a new 'CF' whose convergents are
-- the odd-indexed convergents of the original).
oddCF :: Fractional a => CF a -> CF a
oddCF = snd . partitionCF


-- * Evaluating continued fractions

-- |Evaluate the convergents of a continued fraction using the fundamental
-- recurrence formula:
-- 
-- A0 = b0, B0 = 1
--
-- A1 = b1b0 + a1,  B1 = b1
-- 
-- A{n+1} = b{n+1}An + a{n+1}A{n-1}
--
-- B{n+1} = b{n+1}Bn + a{n+1}B{n-1}
--
-- The convergents are then Xn = An/Bn
convergents :: Fractional a => CF a -> [a]
convergents orig = drop 1 (zipWith (/) nums denoms)
    where
        (b0, terms) = asGCF orig
        nums   = 1:b0:[b * x1 + a * x0 | x0:x1:_ <- tails nums   | (a,b) <- terms]
        denoms = 0:1 :[b * x1 + a * x0 | x0:x1:_ <- tails denoms | (a,b) <- terms]

-- |Evaluate the convergents of a continued fraction using Steed's method.
-- Only valid if the denominator in the following recurrence for D_i never 
-- goes to zero.  If this method blows up, try 'modifiedLentz'.
--
-- D1 = 1/b1
-- 
-- D{i} = 1 / (b{i} + a{i} * D{i-1})
-- 
-- dx1 = a1 / b1
-- 
-- dx{i} = (b{i} * D{i} - 1) * dx{i-1}
-- 
-- x0 = b0
-- 
-- x{i} = x{i-1} + dx{i}
-- 
-- The convergents are given by @scanl (+) b0 dxs@
steed :: Fractional a => CF a -> [a]
steed (CF  b0 []) = [b0]
steed (GCF b0 []) = [b0]
steed (CF  0 (  a  :rest)) = map (1 /) (steed (CF  a rest))
steed (GCF 0 ((a,b):rest)) = map (a /) (steed (GCF b rest))
steed orig
    = scanl (+) b0 dxs
    where
        (b0, (a1,b1):gcf) = asGCF orig
        
        dxs = a1/b1 : [(b * d - 1) * dx  | (a,b) <- gcf | d <- ds | dx <- dxs]
        ds  =  1/b1 : [recip (b + a * d) | (a,b) <- gcf | d <- ds]

-- |Evaluate the convergents of a continued fraction using Lentz's method.
-- Only valid if the denominators in the following recurrence never go to
-- zero.  If this method blows up, try 'modifiedLentz'.
--
-- C1 = b1 + a1 / b0
--
-- D1 = 1/b1
-- 
-- C{n} = b{n} + a{n} / C{n-1}
-- 
-- D{n} = 1 / (b{n} + a{n} * D{n-1})
-- 
-- The convergents are given by @scanl (*) b0 (zipWith (*) cs ds)@
lentz :: Fractional a => CF a -> [a]
lentz = lentzWith id (*) recip

-- |Evaluate the convergents of a continued fraction using Lentz's method,
-- mapping the terms in the final product to a new group before performing
-- the final multiplications.  A useful group, for example, would be logarithms
-- under addition.  In @lentzWith f op inv@, the arguments are:
-- 
-- * @f@, a group homomorphism (eg, 'log') from {@a@,(*),'recip'} to the group
--   in which you want to perform the multiplications.
-- 
-- * @op@, the group operation (eg., (+)).
-- 
-- * @inv@, the group inverse (eg., 'negate').
-- 
-- The 'lentz' function, for example, is given by the identity homomorphism:
-- @lentz@ = @lentzWith id (*) recip@.
-- 
-- The original motivation for this function is to allow computation of 
-- the natural log of very large numbers that would overflow with the naive
-- implementation in 'lentz'.  In this case, the arguments would be 'log', (+),
-- and 'negate', respectively.
-- 
-- In cases where terms of the product can be negative (i.e., the sequence of
-- convergents contains negative values), the following definitions could 
-- be used instead:
-- 
-- > signLog x = (signum x, log (abs x))
-- > addSignLog (xS,xL) (yS,yL) = (xS*yS, xL+yL)
-- > negateSignLog (s,l) = (s, negate l)
{-# INLINE lentzWith #-}
lentzWith :: Fractional a => (a -> b) -> (b -> b -> b) -> (b -> b) -> CF a -> [b]
lentzWith f op inv (CF  0 (  a  :rest)) = map inv              (lentzWith f op inv (CF  a rest))
lentzWith f op inv (GCF 0 ((a,b):rest)) = map (op (f a) . inv) (lentzWith f op inv (GCF b rest))
lentzWith f op inv c = scanl opF (f b0) (zipWith (*) cs ds)
   where
       opF x y = op x (f y)
       (b0, cs, ds) = lentzRecurrence c


-- precondition: b0 /= 0
lentzRecurrence :: Fractional a => CF a -> (a,[a],[a])
lentzRecurrence orig 
    | null terms    = (b0,[],[])
    | otherwise = (b0, cs, ds)
    where
        (b0, terms) = asGCF orig
        
        cs = [   b + a/c  | (a,b) <- terms | c <- b0 : cs]
        ds = [1/(b + a*d) | (a,b) <- terms | d <- 0  : ds]


-- |Evaluate the convergents of a continued fraction using Lentz's method,
-- (see 'lentz') with the additional rule that if a denominator ever goes
-- to zero, it will be replaced by a (very small) number of your choosing,
-- typically 1e-30 or so (this modification was proposed by Thompson and 
-- Barnett).  
-- 
-- Additionally splits the resulting list of convergents into sublists, 
-- starting a new list every time the \'modification\' is invoked.  
modifiedLentz :: Fractional a => a -> CF a -> [[a]]
modifiedLentz = modifiedLentzWith id (*) recip

-- |'modifiedLentz' with a group homomorphism (see 'lentzWith', it bears the
-- same relationship to 'lentz' as this function does to 'modifiedLentz',
-- and solves the same problems).  Alternatively, 'lentzWith' with the same
-- modification to the recurrence as 'modifiedLentz'.
{-# INLINE modifiedLentzWith #-}
modifiedLentzWith :: Fractional a => (a -> b) -> (b -> b -> b) -> (b -> b) -> a -> CF a -> [[b]]
modifiedLentzWith f op inv z (CF  0 (  a  :rest)) = map (map             inv ) (modifiedLentzWith f op inv z (CF  a rest))
modifiedLentzWith f op inv z (GCF 0 ((a,b):rest)) = map (map (op (f a) . inv)) (modifiedLentzWith f op inv z (GCF b rest))
modifiedLentzWith f op inv z orig = separate (scanl opF (False, f b0) cds)
    where
        (b0, cs, ds) = modifiedLentzRecurrence z orig
        cds = zipWith mult cs ds
        
        mult (xa,xb) (ya,yb) = (xa || ya, xb * yb)
        opF  (xa,xb) (ya,yb) = (xa || ya, op xb (f yb))
        
        -- |Takes a list of (Bool,a) and breaks it into sublists, starting
        -- a new one every time it encounters (True,_).
        separate [] = []
        separate ((_,x):xs) = case break fst xs of
            (xs, ys) -> (x:map snd xs) : separate ys

-- precondition: b0 /= 0
modifiedLentzRecurrence :: Fractional a => a -> CF a -> (a,[(Bool, a)],[(Bool, a)])
modifiedLentzRecurrence z orig
    | null terms = (b0, [], [])
    | otherwise  = (b0, cs, ds)
    where
        (b0, terms) = asGCF orig
        
        cs = [reset (b + a/c)    id | (a,b) <- terms | c <- b0 : map snd cs]
        ds = [reset (b + a*d) recip | (a,b) <- terms | d <- 0  : map snd ds]
        
        -- The sublist breaking is computed secondarily - initially, 
        -- 'cs' and 'ds' are constructed with this helper function that
        -- adds a marker to the list whenever a term of interest goes to 0,
        -- while also resetting that term to a small nonzero amount.
        -- Then later, 'separate' breaks the list every time it sees one
        -- of these markers.
        reset x f
            | x == 0    = (True,  f z)
            | otherwise = (False, f x)


-- |Euler's formula for computing @sum (scanl1 (*) xs)@.  
-- Successive convergents of the resulting 'CF' are successive partial sums
-- in the series.
sumPartialProducts :: Num a => [a] -> CF a
sumPartialProducts [] = cf 0 []
sumPartialProducts (x:xs) = gcf 0 ((x,1):[(negate x, 1 + x) | x <- xs])