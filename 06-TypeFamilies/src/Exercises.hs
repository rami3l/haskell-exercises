{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

module Exercises where

import Data.Kind (Constraint, Type)
import Data.Type.Bool (If, Not)
import Data.Type.Equality (type (:~:) (Refl), type (==))

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
  S x + y = S (x + y)

type (-) :: Nat -> Nat -> Nat
type family x - y where
  x - Z = x
  S x - S y = x - y

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
  _ `Delete` Empty = Empty
  _ `Delete` Node Empty _ r = r
  x `Delete` Node l x r = Node (TMaximum l `Delete` l) (TMaximum l) r
  x `Delete` Node l y r = If (x `Compare` y == LT) (Node (x `Delete` l) y r) (Node l y (x `Delete` r))

type TMaximum :: Tree -> Nat
type family TMaximum xs where
  TMaximum Empty = Z
  TMaximum (Node _ x Empty) = x
  TMaximum (Node _ _ r) = TMaximum r

-- Below are some proofs!
type ATree = Node (Node Empty Three Empty) Five (Node Empty Seven Empty)

insertTest0 ::
  Six `Insert` ATree
    :~: Node
          (Node Empty Three Empty)
          Five
          (Node (Node Empty Six Empty) Seven Empty)
insertTest0 = Refl

insertTest1 ::
  One `Insert` ATree
    :~: Node
          (Node (Node Empty One Empty) Three Empty)
          Five
          (Node Empty Seven Empty)
insertTest1 = Refl

insertTest2 :: Five `Insert` ATree :~: ATree
insertTest2 = Refl

deleteTest0 :: Delete Z Empty :~: Empty
deleteTest0 = Refl

deleteTest1 :: Delete Z (Insert Z Empty) :~: Empty
deleteTest1 = Refl

deleteTest2 :: Insert Z (Insert Z Empty) :~: Insert Z Empty
deleteTest2 = Refl

deleteTest3 ::
  Insert (S Z) (Insert Z Empty)
    :~: 'Node 'Empty Z (Node Empty (S Z) Empty)
deleteTest3 = Refl

deleteTest4 :: Five `Delete` ATree :~: Node Empty Three (Node Empty Seven Empty)
deleteTest4 = Refl

{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.
type HList :: [Type] -> Type
data HList xs where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x : xs)

-- Originally:
-- type (++) :: [Type] -> [Type] -> [Type]

-- Changed to the following for Q9 (exploiting @PolyKinds@):
type (++) :: [k] -> [k] -> [k]
type family as ++ bs where
  '[] ++ bs = bs
  (a : as) ++ bs = a : as ++ bs

-- | Write a function that appends two 'HList's.
happend :: HList as -> HList bs -> HList (as ++ bs)
HNil `happend` bs = bs
(HCons a as) `happend` bs = HCons a $ as `happend` bs

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
type CAppend :: Constraint -> Constraint -> Constraint
type family x `CAppend` y where
  x `CAppend` y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.

-- Copied from @Relude.Extra.Type.AllHave@:
type AllHave :: (k -> Constraint) -> [k] -> Constraint
type family f `AllHave` xs where
  _ `AllHave` '[] = ()
  f `AllHave` (x : xs) = (f x, f `AllHave` xs)

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
instance Show `AllHave` as => Show (HList as) where
  show HNil = "HNil"
  show (HCons a as) =
    "HCons " ++ show a ++ " " ++ case as of
      HNil -> show as
      _ -> "(" ++ show as ++ ")"

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance Eq `AllHave` as => Eq (HList as) where
  HNil == HNil = True
  HCons a as == HCons b bs = a == b && as == bs

instance (Eq `AllHave` as, Ord `AllHave` as) => Ord (HList as) where
  HNil `compare` HNil = EQ
  HCons a as `compare` HCons b bs = (a `compare` b) <> (as `compare` bs)

-- In practice, these implementations are so trivial that GHC can even derive them:

-- deriving instance Show `AllHave` as => Show (HList as)
-- deriving instance Eq `AllHave` as => Eq (HList as)
-- deriving instance (Eq `AllHave` as, Ord `AllHave` as) => Ord (HList as)
{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type UpTo :: Nat -> [Nat]
type family UpTo x where
  UpTo Z = '[Z]
  UpTo (S x) = UpTo x ++ '[S x]

-- | b. Write a type-level prime number sieve.

-- sieve (x:xs) = x:(sieve $ filter (\a -> a `mod` x /= 0) xs)
type PrimesUpTo :: Nat -> [Nat]
type family PrimesUpTo x where
  PrimesUpTo x = Sieve ((Drop Two) (UpTo x))

type Drop :: Nat -> [k] -> [k]
type family Drop n xs where
  Drop _ '[] = '[]
  Drop Z xs = xs
  Drop (S n) (x : xs) = Drop n xs

type Sieve :: [Nat] -> [Nat]
type family Sieve xs where
  Sieve '[] = '[]
  Sieve (x : xs) = x : Sieve (DropEvery x xs)

type DropEvery :: Nat -> [Nat] -> [Nat]
type family DropEvery n xs where
  DropEvery n xs = DropEvery' n n xs

type DropEvery' :: Nat -> Nat -> [Nat] -> [Nat]
type family DropEvery' n c xs where
  DropEvery' n _ '[] = '[]
-- Every time the counter @c@ drops to 'One', a term is skipped and @c@ is reset to @n@.
  DropEvery' n One (x : xs) = DropEvery' n n xs
  DropEvery' n (S c) (x : xs) = x : DropEvery' n c xs

testSieve :: PrimesUpTo Ten :~: '[Two, Three, Five, Seven]
testSieve = Refl

-- | c. Why is this such hard work?

-- I think it boils down to a few things:
--
-- * No let-binding at the type level.
--
-- * No higher-order functions - I can't write higher-order helpers without
--   running into complaints about type families not having all their
--   arguments. Recent work on unsaturated type families (type families without
--   all their arguments) promises a solution to this, though!
--
-- * Syntax!