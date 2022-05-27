{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

module Exercises where

import Data.Kind (Constraint, Type)
import Data.Type.Bool (If)
import Data.Type.Equality (type (==))

-- | Before we get started, let's talk about the @TypeOperators@ extension. All
-- this does is allow us to write types whose names are operators, and write
-- regular names as infix names with the backticks, as we would at the value
-- level.

{- ONE -}

data Nat = Z | S Nat

type One = S Z

type Two = S One

type Three = S Two

type Four = S Three

type Five = S Four

type Six = S Five

type Seven = S Six

type Eight = S Seven

type Nine = S Eight

type Ten = S Nine

-- | a. Use the @TypeOperators@ extension to rewrite the 'Add' family with the
-- name '+':
type (+) :: Nat -> Nat -> Nat
type family x + y where
  Z + y = y
  (S x) + y = S (x + y)

-- | b. Write a type family '*' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?
type SNat :: Nat -> Type
data SNat value where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

type (*) :: Nat -> Nat -> Nat
type family x * y where
  Z * _ = Z
  S x * y = y + (x * y)

-- | c. Write a function to add two 'SNat' values.
sadd :: SNat x -> SNat y -> SNat (x + y)
sadd SZ y = y
sadd (SS x) y = SS (x `sadd` y)

{- TWO -}

type Vector :: Nat -> Type -> Type
data Vector count a where
  VNil :: Vector Z a
  VCons :: a -> Vector n a -> Vector (S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?
append :: Vector m a -> Vector n a -> Vector (m + n) a
VNil `append` v = v
VCons a as `append` bs = VCons a $ as `append` bs

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.

-- This should've typechecked but didn't:
-- flatMap :: (a -> Vector m b) -> Vector n a  -> Vector (m*n) b
-- f `flatMap` VNil = VNil
-- f `flatMap` VCons a as = (f a) `append` (f `flatMap` as)

-- | This is a really interesting problem, and really exposes the problems we
-- have in type-level programming: we can't convince GHC that @x + y == y + x@,
-- or that @x + (y + z) == (x + y) + z@, without providing a very explicit
-- proof. It just so happens that, if we define `*` with the successor's
-- recursive step on the /right/ (as above), we're fine and don't need to do
-- any of this hard work. Unfortunately, though, we'll regularly be less lucky.
--
-- This is irritating enough that libraries (or, rather, plugins) such as
-- http://hackage.haskell.org/package/ghc-typelits-natnormalise exist purely to
-- avoid these messes.
flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n * m) b
flatMap VNil _ = VNil
flatMap (VCons x xs) f = f x `append` flatMap xs f

{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type (&&) :: Bool -> Bool -> Bool
type family x && y where
  True && True = True
  _ && _ = False

-- | b. Write the type-level @||@ function for booleans.
type (||) :: Bool -> Bool -> Bool
type family x || y where
  False || False = False
  _ || _ = True

-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type All :: [Bool] -> Bool
type family All bs where
  All '[] = True
  All (b : bs) = b && All bs

{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.
type Compare :: Nat -> Nat -> Ordering
type family x `Compare` y where
  Z `Compare` Z = EQ
  Z `Compare` _ = LT
  _ `Compare` Z = GT
  S x `Compare` S y = x `Compare` y

-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type Max :: Nat -> Nat -> Nat
type family x `Max` y where
  x `Max` y = If (x `Compare` y == LT) y x

-- | c. Write a family to get the maximum natural in a list.
type Maximum :: [Nat] -> Nat
type family Maximum xs where
  Maximum '[] = Z
  Maximum (x : xs) = x `Max` Maximum xs

{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type Insert :: Nat -> Tree -> Tree
type family x `Insert` xs where
  x `Insert` Empty = Node Empty x Empty
  x `Insert` Node l y r =
    If
      (x `Compare` y == LT)
      (Node (x `Insert` l) y r)
      ( If
          (x `Compare` y == GT)
          (Node l y (x `Insert` r))
          (Node l y r)
      )

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type Delete :: Nat -> Tree -> Tree
type family x `Delete` xs where
  x `Delete` Empty = Empty
  x `Delete` Node Empty _ r = r
  x `Delete` Node l x r = Node (TMaximum l `Delete` l) (TMaximum l) r
  x `Delete` Node l y r = If (x `Compare` y == LT) (Node (x `Delete` l) y r) (Node l y (x `Delete` r))

type TMaximum :: Tree -> Nat
type family TMaximum xs where
  TMaximum Empty = Z
  TMaximum (Node _ x Empty) = x
  TMaximum (Node _ _ r) = TMaximum r

{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.
data HList (xs :: [Type]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Write a function that appends two 'HList's.

{- EIGHT -}

-- | Type families can also be used to build up constraints. There are, at this
-- point, a couple things that are worth mentioning about constraints:
--
-- - As we saw before, '()' is the empty constraint, which simply has "no
--   effect", and is trivially solved.
--
-- - Unlike tuples, constraints are "auto-flattened": ((a, b), (c, (d, ())) is
--   exactly equivalent to (a, b, c, d). Thanks to this property, we can build
--   up constraints using type families!
type family CAppend (x :: Constraint) (y :: Constraint) :: Constraint where
  CAppend x y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.
type family Every (c :: Type -> Constraint) (x :: [Type]) :: Constraint where

-- ...

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?

{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.

-- | b. Write a type-level prime number sieve.

-- | c. Why is this such hard work?