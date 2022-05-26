{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Exercises where

import Data.Function ((&))
import Data.Kind (Type)
import Data.Void (Void, absurd)
import GHC.Types (Constraint)
import Prelude hiding ((!!))

{- ONE -}

-- | One of the restrictions around classes that we occasionally hit is that we
-- can only have one instance for a type. There are, for example, two good
-- candidates for a monoid instance when we think about 'Integer':
data IntegerMonoidKind = Sum | Product

-- | a. Write a newtype around 'Integer' that lets us choose which instance we
-- want.
-- NOTE: New syntax enabled by @{-# LANGUAGE StandaloneKindSignatures #-}@
type IntegerMonoid :: IntegerMonoidKind -> Type
newtype IntegerMonoid m = IntegerMono Integer

-- | b. Write the two monoid instances for 'Integer'.
instance Semigroup (IntegerMonoid Sum) where
  IntegerMono i <> IntegerMono j = IntegerMono $ i + j

instance Monoid (IntegerMonoid Sum) where
  mempty = IntegerMono 0

instance Semigroup (IntegerMonoid Product) where
  IntegerMono i <> IntegerMono j = IntegerMono $ i * j

instance Monoid (IntegerMonoid Product) where
  mempty = IntegerMono 1

-- | c. Why do we need @FlexibleInstances@ to do this?

{- TWO -}

-- | We can write a type that /is/ of kind 'Type', but has no value-level
-- members. We usually call this type 'Void':
data Void' -- No constructors!

-- | a. If we promote this with DataKinds, can we produce any /types/ of kind
-- 'Void'?
class UseVoid (a :: Void')

-- Cannot define an instance because @Void@ has no constructors.

-- | b. What are the possible type-level values of kind 'Maybe Void'?
maybeVoid :: Maybe Void
maybeVoid = Nothing

-- | c. Considering 'Maybe Void', and similar examples of kinds such as
-- 'Either Void Bool', why do you think 'Void' might be a useful kind?
justBool :: Either Void Bool -> Bool
justBool (Left l) = absurd l
justBool (Right b) = b

{- THREE -}

-- | a. Write a GADT that holds strings or integers, and keeps track of how
-- many strings are present. Note that you might need more than 'Nil' and
-- 'Cons' this time...
data Nat = Z | S Nat deriving (Show)

-- | b. Update it to keep track of the count of strings /and/ integers.
data StringAndIntList (stringCount :: Nat) (intCount :: Nat) where
  SINil :: StringAndIntList Z Z
  SCons :: String -> StringAndIntList s i -> StringAndIntList (S s) i
  ICons :: Integer -> StringAndIntList s i -> StringAndIntList s (S i)

deriving instance Show (StringAndIntList s i)

-- | c. What would be the type of the 'head' function?
head :: StringAndIntList s i -> Maybe (Either String Integer)
head SINil = Nothing
head (SCons s _) = Just $ Left s
head (ICons i _) = Just $ Right i

{- FOUR -}

-- | When we talked about GADTs, we discussed existentials, and how we could
-- only know something about our value if the context told us:
-- data Showable where Showable :: Show a => a -> Showable

-- | a. Write a GADT that holds something that may or may not be showable, and
-- stores this fact in the type-level.
data MaybeShowable (isShowable :: Bool) where
  Showable :: Show a => a -> MaybeShowable True
  -- It seems impossible to enforce that @a@ be not @Show@able.
  NotShowable :: a -> MaybeShowable False

-- ...

-- | b. Write a 'Show' instance for 'MaybeShowable'. Your instance should not
-- work unless the type is actually 'show'able.
instance Show (MaybeShowable True) where
  show (Showable a) = "Showable " ++ show a ++ ""

-- | c. What if we wanted to generalize this to @Constrainable@, such that it
-- would work for any user-supplied constraint of kind 'Constraint'? How would
-- the type change? What would the constructor look like? Try to build this
-- type - GHC should tell you exactly which extension you're missing.
data Constrainable (pred :: Type -> Constraint) where
  Constrainable :: pred a => a -> Constrainable pred

{- FIVE -}

-- | Recall our list type:
data List a = Nil | Cons a (List a)

-- | a. Use this to write a better 'HList' type than we had in the @GADTs@
-- exercise. Bear in mind that, at the type-level, 'Nil' and 'Cons' should be
-- "ticked". Remember also that, at the type-level, there's nothing weird about
-- having a list of types!
data HList (types :: List Type) where
  HNil :: HList Nil
  HCons :: a -> HList as -> HList (Cons a as)

-- | b. Write a well-typed, 'Maybe'-less implementation for the 'tail' function
-- on 'HList'.
htail :: HList (Cons a as) -> HList as
htail (HCons a as) = as

-- | c. Could we write the 'take' function? What would its type be? What would
-- get in our way?
-- This will eventually happen in chapter 10.

{- SIX -}

-- | Here's a boring data type:

{-
data BlogAction
  = AddBlog
  | DeleteBlog
  | AddComment
  | DeleteComment
-}

-- | a. Two of these actions, 'DeleteBlog' and 'DeleteComment', should be
-- admin-only. Extend the 'BlogAction' type (perhaps with a GADT...) to
-- express, at the type-level, whether the value is an admin-only operation.
-- Remember that, by switching on @DataKinds@, we have access to a promoted
-- version of 'Bool'!
data AccessLevel = Admin | User | Moderator

data BlogAction (ls :: [AccessLevel]) where
  AddBlog :: BlogAction [User, Moderator, Admin]
  DeleteBlog :: BlogAction '[Admin]
  AddComment :: BlogAction [User, Moderator, Admin]
  DeleteComment :: BlogAction [Moderator, Admin]

-- | b. Write a 'BlogAction' list type that requires all its members to be
-- the same "access level": "admin" or "non-admin".
newtype BlogActionList (ls :: [AccessLevel]) = BlogActionList [BlogAction ls]

-- | c. Let's imagine that our requirements change, and 'DeleteComment' is now
-- available to a third role: moderators. Could we use 'DataKinds' to introduce
-- the three roles at the type-level, and modify our type to keep track of
-- this?

{- SEVEN -}

-- | When we start thinking about type-level Haskell, we inevitably end up
-- thinking about /singletons/. Singleton types have a one-to-one value-type
-- correspondence - only one value for each type, only one type for each value.
-- A simple example is '()', whose only value is '()'. 'Bool' is /not/ a
-- singleton, because it has multiple values.

-- We can, however, /build/ a singleton type for 'Bool':

data SBool (value :: Bool) where
  SFalse :: SBool False
  STrue :: SBool True

-- | a. Write a singleton type for natural numbers:
data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- | b. Write a function that extracts a vector's length at the type level:
vlength :: Vector n a -> SNat n
vlength VNil = SZ
vlength (VCons a as) = SS (vlength as)

-- | c. Is 'Proxy' a singleton type?
data Proxy a = Proxy

-- No - @Proxy :: Proxy Int@ and @Proxy :: Proxy String@ have the same value-level representation.
-- Thus, the correspondence is not one-to-one.

{- EIGHT -}

-- | Let's imagine we're writing some Industry Haskell™, and we need to read
-- and write to a file. To do this, we might write a data type to express our
-- intentions:

{-
data Program result
  = OpenFile (Program result)
  | WriteFile String (Program result)
  | ReadFile (String -> Program result)
  | CloseFile (Program result)
  | Exit result
-}
data Program (fileOpen :: Bool) r where
  -- The execution order of the program seems to be outside in, so the arrow direction
  -- here is also a bit counterintuitive...
  OpenFile :: Program True r -> Program False r
  WriteFile :: String -> Program True r -> Program True r
  ReadFile :: (String -> Program True r) -> Program True r
  CloseFile :: Program False r -> Program True r
  Exit :: r -> Program False r

-- | We could then write a program like this to use our language:
myApp :: Program False Bool
myApp =
  OpenFile . WriteFile "HEY" $
    ReadFile
      ( \contents ->
          if contents == "WHAT"
            then WriteFile "... bug?" $ CloseFile $ Exit False
            else CloseFile $ Exit True
      )

-- | ... but wait, there's a bug! If the contents of the file equals "WHAT", we
-- forget to close the file! Ideally, we would like the compiler to help us: we
-- could keep track of whether the file is open at the type level!
--
-- - We should /not/ be allowed to open a file if another file is currently
-- open.
--
-- - We should /not/ be allowed to close a file unless a file is open.
--
-- If we had this at the type level, the compiler should have been able to tell
-- us that the branches of the @if@ have different types, and this program
-- should never have made it into production. We should also have to say in the
-- type of 'myApp' that, once the program has completed, the file will be
-- closed.

-- | Improve the 'Program' type to keep track of whether a file is open.  Make
-- sure the constructors respect this flag: we shouldn't be able to read or
-- write to the file unless it's open. This exercise is a bit brain-bending;
-- why? How could we make it more intuitive to write?

-- | EXTRA: write an interpreter for this program. Nothing to do with data
-- kinds, but a nice little problem.

{- interpret :: Program {- ??? -} a -> IO a
interpret = error "Implement me?"
-}

{- NINE -}

-- | Recall our vector type:
data Vector (n :: Nat) (a :: Type) where
  VNil :: Vector Z a
  VCons :: a -> Vector n a -> Vector (S n) a

-- | Imagine we want to write the '(!!)' function for this vector. If we wanted
-- to make this type-safe, and avoid 'Maybe', we'd have to have a type that can
-- only hold numbers /smaller/ than some type-level value.

-- | a. Implement this type! This might seem scary at first, but break it down
-- into Z and S cases. That's all the hint you need :)
data SmallerThan (lim :: Nat) where
  -- NOTE: Consider this as a PROOF!!! (cf. https://plfa.github.io/Relations)
  -- 0 < n + 1
  ZltS :: SmallerThan (S n)
  -- x < n ⇒ x + 1 < n + 1
  SltS :: SmallerThan n -> SmallerThan (S n)

-- | b. Write the '(!!)' function:
(!!) :: Vector n a -> SmallerThan n -> a
VCons a _ !! ZltS = a
VCons _ as !! SltS n = as !! n

-- An example of using the '(!!)' function:
type Two = S (S Z)

type Five = S (S (S Two))

aVector :: Vector Five Int
aVector = VNil & VCons 4 & VCons 3 & VCons 2 & VCons 1 & VCons 0

threeLtFive :: SmallerThan Five
threeLtFive = (ZltS :: SmallerThan Two {- 0 < 2 -}) & SltS {- 1 < 3 -} & SltS {- 2 < 4 -} & SltS {- 3 < 5 -}

getThird :: Int
getThird = aVector !! threeLtFive

-- | c. Write a function that converts a @SmallerThan n@ into a 'Nat'.
sup :: SmallerThan lim -> Nat
sup ZltS = Z
sup (SltS n) = S $ sup n