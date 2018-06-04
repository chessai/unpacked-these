{-# LANGUAGE KindSignatures #-}

module Main (main) where

import Control.Applicative
import Control.Monad (liftM)
import Data.Functor.Classes
import Data.These.Unpacked
import Data.Proxy (Proxy(..))
import Data.Semigroup (Semigroup((<>)))
import Test.QuickCheck.Classes
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen

main :: IO ()
main = lawsCheckMany myClassTests

myClassTests :: [(String, [Laws])]
myClassTests =
  [ ("Ground types", myLaws theseProxy)
--  , ("Higher-kinded types", myLaws1 theseProxy1)
  ]

myLaws
  :: (Arbitrary a, Eq a, Ord a, Show a, Read a)
  => Proxy a -> [Laws]
myLaws p =
  [ eqLaws p
  , ordLaws p
  , showReadLaws p
  ]

--myLaws1
--  :: (Arbitrary1 a, Monad a, Functor a, Applicative a, Foldable a, Traversable a, Eq1 a, Show1 a)
--  => Proxy a -> [Laws]
--myLaws1 p =
--  [ monadLaws p
--  , functorLaws p
--  , applicativeLaws p
--  , foldableLaws p
--  , traversableLaws p
--  ]

theseProxy2 :: Proxy These
theseProxy2 = Proxy

theseProxy1 :: Proxy (These Int)
theseProxy1 = Proxy

theseProxy  :: Proxy (These Int Int)
theseProxy  = Proxy

instance Semigroup Int where
  (<>) = (+)

instance Monoid Int where
  mempty = 0
  mappend = (+)

instance Arbitrary2 These where
    liftArbitrary2 arbA arbB = oneof
        [ This <$> arbA
        , That <$> arbB
        , Both <$> arbA <*> arbB
        ]

    liftShrink2  shrA _shrB (This x) = This <$> shrA x
    liftShrink2 _shrA  shrB (That y) = That <$> shrB y
    liftShrink2  shrA  shrB (Both x y) =
        [This x, That y] ++ [Both x' y' | (x', y') <- liftShrink2 shrA shrB (x, y)]

instance (Arbitrary a) => Arbitrary1 (These a) where
    liftArbitrary = liftArbitrary2 arbitrary
    liftShrink = liftShrink2 shrink

instance (Arbitrary a, Arbitrary b) => Arbitrary (These a b) where
    arbitrary = arbitrary1
    shrink = shrink1
