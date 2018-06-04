--------------------------------------------------------------------------------

-- Copyright © 2018 Daniel Cartwright

-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
-- 
--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.
-- 
--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.
-- 
--     * Neither the name of Kyle McKean nor the names of other
--       contributors may be used to endorse or promote products derived
--       from this software without specific prior written permission.
-- 
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
-- A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
-- OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
-- SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
-- LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
-- DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
-- THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

--------------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -O2 #-}

--------------------------------------------------------------------------------

{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE MagicHash          #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE UnboxedSums        #-}
{-# LANGUAGE UnboxedTuples      #-}

--------------------------------------------------------------------------------

-- | Module     :  Data.These.Unpacked
--
-- The 'These' type and associated operations. 
--
-- This module is intended to be a drop-in(*) replacement for /Data.These/. To shave off pointer chasing, it uses -XUnboxedSums to represent the 'These' type as two machine words that are contiguous in memory, without loss of expressiveness that 'These' provides.
--
-- This library provides pattern synonyms This, That, and Both(*), which allow users to pattern match on an Unpacked These in a familiar way.
-- 
-- Functions are also provided for converting an Unpacked These to the these library's These, and vice versa.
--
-- (*): pattern synonyms use the same namespace as type constructors, so pattern matching on an Unpacked These with the more familiar 'These' data constructor is not possible, instead, Both is provided.
--
-- This library is in alpha, and the internals are likely to change.
module Data.These.Unpacked
  ( These(This,That,Both)

    -- * Consumption
  , these
  , fromThese
  , mergeThese
  , mergeTheseWith

    -- * Traversals
  , here
  , there

    -- * Case selections
  , justThis
  , justThat
  , justThese
  
  , catThis
  , catThat
  , catThese

  , partitionThese 
  
    -- * Case predicates 
  , isThis
  , isThat
  , isThese

    -- * Map operations
  , mapThese
  , mapThis
  , mapThat
  
    -- * Conversions
  , fromBaseThese
  , toBaseThese
  ) where

--------------------------------------------------------------------------------

import Prelude
  (seq)

import           Control.Applicative (Applicative((<*>), pure))
import           Control.DeepSeq     (NFData(rnf))
import           Control.Monad       (Monad(return, (>>=)))

import           Data.Bifoldable     (Bifoldable(bifold, bifoldl, bifoldr))
import           Data.Bifunctor      (Bifunctor(bimap, first, second))
import           Data.Bitraversable  (Bitraversable(bitraverse))

import           Data.Bool           (Bool(False), (&&))
import           Data.Data
  ( Data(gfoldl, gunfold, toConstr, dataTypeOf, dataCast2)
  , Constr, mkConstr, constrIndex
  , DataType, mkDataType
  , Fixity(Prefix)
  )
import           Data.Eq             (Eq((==)))
import           Data.Foldable
  (Foldable(foldr))

import           Data.Function       (id, flip, (.), ($))
import           Data.Functor        (Functor(fmap), (<$>))
import           Data.Maybe.Unpacked (Maybe(Just,Nothing), isJust, mapMaybe)
import           Data.Monoid         (Monoid(mappend))
import           Data.Ord            (Ord(compare, (>=)), Ordering(EQ, GT, LT))
import           Data.Semigroup      (Semigroup((<>)))
import qualified Data.These          as BaseThese
import           Data.Traversable    (Traversable(sequenceA, traverse))
import           Data.Typeable       (gcast2)

import           GHC.Base            (Int(I#))
import           GHC.Read            (Read(readPrec), expectP)
import           GHC.Show            (Show(showsPrec), showString, showParen, showSpace)

import           Text.Read           (parens, Lexeme(Ident), (+++), readListPrec, readListDefault, readListPrecDefault)
import qualified Text.Read           as TextRead
import           Text.ParserCombinators.ReadPrec
  (prec, step)

--------------------------------------------------------------------------------

-- | The 'These' type represents values with two non-exclusive possibilities.
--
--   This can be useful to represent combinations of two values, where the
--   combination is defined if either input is. Algebraically, the type
--   @These A B@ represents @(A + B + AB)@, which doesn't factor easily into
--   sums and products--a type like @Either A (B, Maybe A)@ is unclear and
--   awkward to use.
--
--   'These' has straightforward instances of 'Functor', 'Monad', &c., and
--   behaves like a hybrid error/writer monad, as would be expected.
data These a b = These (# a | b | (# a, b #) #)

pattern This :: a -> These a b
pattern This a = These (# a | | #)

pattern That :: b -> These a b
pattern That b = These (# | b | #)

pattern Both :: a -> b -> These a b
pattern Both a b = These (# | | (# a, b #) #)

{-# COMPLETE This, That, Both #-}

-- | Case analysis for the 'These' type.
these :: (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
{-# INLINE these #-}
these fa fb fab (These x) = case x of
  (# a |   |            #) -> fa a
  (#   | b |            #) -> fb b
  (#   |   | (# a, b #) #) -> fab a b

-- | Takes two default values and produces a tuple if the 'These' value is not 'This' or 'That'.
fromThese :: a -> b -> These a b -> (a, b)
{-# INLINE fromThese #-}
fromThese defA defB ths = these (\a -> (a, defB)) (\b -> (defA, b)) (\a b -> (a, b)) ths

-- | Select each constructor and partition them into separate lists.
partitionThese :: [These a b] -> ( [(a, b)], ([a], [b]) )
{-# INLINEABLE [0] partitionThese #-}
partitionThese [] = ([], ([], []))
partitionThese (Both x y : xs) = first  ((x, y)   : ) $ partitionThese xs
partitionThese (This x   : xs) = second (first  (x:)) $ partitionThese xs
partitionThese (That   y : xs) = second (second (y:)) $ partitionThese xs

-- | Coalesce with the provided operation.
mergeThese :: (a -> a -> a) -> These a a -> a
{-# INLINE mergeThese #-}
mergeThese = these id id

-- | bimap and coalesce results with the provided operation.
mergeTheseWith :: (a -> c) -> (b -> c) -> (c -> c -> c) -> These a b -> c
{-# INLINE mergeTheseWith #-}
mergeTheseWith f g op t = mergeThese op $ mapThese f g t

-- | A @Traversal@ of the first half of a 'These', suitable for use with @Control.Lens@.
here :: (Applicative f) => (a -> f b) -> These a t -> f (These b t)
{-# INLINE here #-}
here f = these (\a -> This <$> f a) (\b -> pure (That b)) (\a b -> flip Both b <$> f a)

-- | A @Traversal@ of the second half of a 'These', suitable for use with @Control.Lens@.
there :: (Applicative f) => (a -> f b) -> These t a -> f (These t b)
{-# INLINE there #-}
there f = these (\a -> pure (This a)) (\b -> That <$> f b) (\a b -> Both a <$> f b)

-- | @'justThis' = 'these' 'Just' (\_ -> 'Nothing') (\_ _ -> 'Nothing')@
justThis :: These a b -> Maybe a 
{-# INLINE justThis #-}
justThis = these Just (\_ -> Nothing) (\_ _ -> Nothing)

-- | @'justThat' = 'these' (\_ -> 'Nothing') 'Just' (\_ _ -> 'Nothing')@
justThat :: These a b -> Maybe b
{-# INLINE justThat #-}
justThat = these (\_ -> Nothing) Just (\_ _ -> Nothing)

-- | @'justThese' = 'these' (\_ -> 'Nothing') (\_ -> 'Nothing') (\a b -> 'Just' (a, b))@
justThese :: These a b -> Maybe (a, b)
{-# INLINE justThese #-}
justThese = these (\_ -> Nothing) (\_ -> Nothing) (\a b -> Just (a, b))

-- | @'isThis' = 'isJust' . 'justThis'@
isThis :: These a b -> Bool
{-# INLINE isThis #-}
isThis = isJust . justThis

-- | @'isThat' = 'isJust' . 'justThat'@
isThat :: These a b -> Bool
{-# INLINE isThat #-}
isThat = isJust . justThat

-- | @'isThese' = 'isJust' . 'justThese'@
isThese :: These a b -> Bool
{-# INLINE isThese #-}
isThese = isJust . justThese

-- | 'Bifunctor''s 'bimap'
mapThese :: (a -> c) -> (b -> d) -> These a b -> These c d
{-# INLINE mapThese #-}
mapThese fac fbd = these (This . fac) (That . fbd) (\a b -> Both (fac a) (fbd b))

-- | 'Bifunctor''s 'first'
mapThis :: (a -> c) -> These a b -> These c b
{-# INLINE mapThis #-}
mapThis f = mapThese f id

-- | 'Bifunctor''s 'second'
mapThat :: (b -> d) -> These a b -> These a d
{-# INLINE mapThat #-}
mapThat f = mapThese id f

-- | Select all 'This' constructors from a list.
catThis :: [These a b] -> [a]
{-# INLINE catThis #-}
catThis = mapMaybe justThis

-- | Select all 'That' constructors from a list.
catThat :: [These a b] -> [b]
{-# INLINE catThat #-}
catThat = mapMaybe justThat

-- | Select all 'Both' constructors from a list.
catThese :: [These a b] -> [(a,b)]
{-# INLINE catThese #-}
catThese = mapMaybe justThese

-- | Convert a 'BaseThese.These' from /Data.These/ to a 'These'
fromBaseThese :: BaseThese.These a b -> These a b
fromBaseThese (BaseThese.This  a  ) = This a
fromBaseThese (BaseThese.That    b) = That   b
fromBaseThese (BaseThese.These a b) = Both a b

-- | Convert a 'These' to a 'BaseThese.These' from /Data.These/
toBaseThese :: These a b -> BaseThese.These a b
toBaseThese (This a  ) = BaseThese.This  a
toBaseThese (That   b) = BaseThese.That    b
toBaseThese (Both a b) = BaseThese.These a b

--------------------------------------------------------------------------------

instance (Semigroup a, Semigroup b) => Semigroup (These a b) where
    This a   <> This b   = This (a <> b)
    This a   <> That   y = Both a              y
    This a   <> Both b y = Both (a <> b)       y
    That   x <> This b   = Both       b   x
    That   x <> That   y = That          (x <> y)
    That   x <> Both b y = Both       b  (x <> y)
    Both a x <> This b   = Both (a <> b)  x
    Both a x <> That   y = Both  a       (x <> y)
    Both a x <> Both b y = Both (a <> b) (x <> y)
    {-# INLINE (<>) #-}

instance Functor (These a) where
    fmap _ (This x) = This x
    fmap f (That y) = That (f y)
    fmap f (Both x y) = Both x (f y)
    {-# INLINE fmap #-}

instance Semigroup a => Applicative (These a) where
  pure = That
  {-# INLINE pure #-}
  This a   <*> _        = This a
  That   _ <*> This b   = This b
  That   f <*> That   x = That (f x)
  That   f <*> Both b x = Both b (f x)
  Both a _ <*> This b   = This (a <> b)
  Both a f <*> That   x = Both a (f x)
  Both a f <*> Both b x = Both (a <> b) (f x)
  {-# INLINE (<*>) #-}

instance Semigroup a => Monad (These a) where
  return = That
  {-# INLINE return #-}
  This a   >>= _ = This a
  That   x >>= k = k x
  Both a x >>= k = case k x of
    This b   -> This (a <> b)
    That   y -> Both a y
    Both b y -> Both (a <> b) y 
  {-# INLINE (>>=) #-}

instance Foldable (These a) where
    foldr _ z (This _) = z
    foldr f z (That x) = f x z
    foldr f z (Both _ x) = f x z
    {-# INLINE foldr #-}

instance Traversable (These a) where
    traverse _ (This a) = pure $ This a
    traverse f (That x) = That <$> f x
    traverse f (Both a x) = Both a <$> f x
    {-# INLINE traverse #-} 
    sequenceA (This a) = pure $ This a
    sequenceA (That x) = That <$> x
    sequenceA (Both a x) = Both a <$> x
    {-# INLINE sequenceA #-}

instance Bifunctor These where
    bimap = mapThese
    {-# INLINE bimap #-} 
    first = mapThis
    {-# INLINE first #-}
    second = mapThat
    {-# INLINE second #-}

instance Bifoldable These where
    bifold = these id id mappend
    {-# INLINE bifold #-}
    bifoldr f g z = these (`f` z) (`g` z) (\x y -> x `f` (y `g` z))
    {-# INLINE bifoldr #-}
    bifoldl f g z = these (z `f`) (z `g`) (\x y -> (z `f` x) `g` y)
    {-# INLINE bifoldl #-}

instance Bitraversable These where
    bitraverse f _ (This x)   = This <$> f x
    bitraverse _ g (That x)   = That <$> g x
    bitraverse f g (Both x y) = Both <$> f x <*> g y

instance (NFData a, NFData b) => NFData (These a b) where
    rnf (This a  ) = rnf a
    rnf (That   b) = rnf b
    rnf (Both a b) = rnf a `seq` rnf b

--------------------------------------------------------------------------------

instance (Eq a, Eq b) => Eq (These a b) where
  This a   == This b     = a == b
  That a   == That b     = a == b
  Both a b == Both a' b' = a == a' && b == b'
  _        ==          _ = False   
  {-# INLINE (==) #-}

instance (Ord a, Ord b) => Ord (These a b) where
  compare x y
    = case x of
        This a -> case y of
          This b -> compare a b
          _      -> LT
        That a -> case y of
          This {} -> GT
          That b  -> compare a b
          _       -> LT
        Both a b -> case y of
          Both a' b' -> case (compare a a') of
            LT -> LT
            EQ -> compare b b'
            GT -> GT
          _ -> GT
  {-# INLINE compare #-}

instance (Read a, Read b) => Read (These a b) where
  readPrec
      = parens
          (prec
             10
             (do expectP (Ident "This")
                 a <- step readPrec
                 return (This a))
             +++
               (prec
                  10
                  (do expectP (Ident "That")
                      b <- step readPrec
                      return (That b))
                  +++
                    prec
                      10
                      (do expectP (Ident "These")
                          a <- step readPrec
                          b <- step readPrec
                          return (Both a b))))
  readList = readListDefault
  readListPrec = readListPrecDefault

instance (Show a, Show b) => Show (These a b) where
  showsPrec i (This a)   = showParen (i >= 11) ((.) (showString "This " ) (showsPrec 11 a))
  showsPrec i (That b)   = showParen (i >= 11) ((.) (showString "That " ) (showsPrec 11 b))
  showsPrec i (Both a b) = showParen (i >= 11) ((.) (showString "These ") ((.) (showsPrec 11 a) ((.) showSpace (showsPrec 11 b))))

instance (Data a, Data b) => Data (These a b) where
  gfoldl  k z (This a)   = z This `k` a
  gfoldl  k z (That b)   = z That `k` b
  gfoldl  k z (Both a b) = (z Both `k` a) `k` b
  gunfold k z c          = case constrIndex c of
    I# 1# -> k (z This)
    I# 2# -> k (z That)
    _    -> k (k (z Both))
  toConstr (This _)   = cThis
  toConstr (That _)   = cThat
  toConstr (Both _ _) = cThese
  dataTypeOf _ = tThese
  dataCast2  f = gcast2 f

tThese :: DataType
tThese = mkDataType "These" [cThis, cThat, cThese]

cThis, cThat, cThese :: Constr
cThis  = mkConstr tThese "This"  [] Prefix
cThat  = mkConstr tThese "That"  [] Prefix
cThese = mkConstr tThese "These" [] Prefix
