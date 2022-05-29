{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Exercises where

import Data.Kind (Type, Constraint)
import GHC.Generics (Generic (..))
import qualified GHC.Generics as G
import GHC.TypeLits ( Symbol, ErrorMessage(..), TypeError )

{- ONE -}

-- | Recall an old friend, the 'Newtype' class:

type Newtype :: Type -> Type -> Constraint
class Newtype new old | new -> old where
  wrap :: old -> new
  unwrap :: new -> old

-- | a. Can we add a functional dependency to this class?

-- | b. Why can't we add two?

-- We wouldn't want to! It's very useful to be able to add multiple newtypes
-- around the /same/ old type - for example, we might want to make sure we
-- don't confuse two 'Double' values when one is being used as a distance and
-- the other as a time duration.

{- TWO -}

-- | Let's go back to a problem we had in the last exercise, and imagine a very
-- simple cache in IO. Uncomment the following:

type Cache :: Type -> Type -> (Type -> Type) -> Constraint
class Cache item uid f | item -> uid where
  store :: item  -> f ()
  load :: uid -> f (Maybe item)

-- | a. Uh oh - there's already a problem! Any @entity@ type should have a
-- fixed type of id/@index@, though... if only we could convince GHC... Could
-- you have a go?

-- | b. @IO@ is fine, but it would be nice if we could choose the functor when
-- we call @store@ or @load@... can we parameterise it in some way?

-- | c. Is there any sort of functional dependency that relates our
-- parameterized functor to @entity@ or @index@? If so, how? If not, why not?

-- | No, and nor would we want one - it would be nice to pick the functor for
-- the same entity/index pair to be different things depending on, say, whether
-- we're running a test or in production.

{- THREE -}

-- | Let's re-introduce one of our old favorites:
data Nat = Z | S Nat

-- | When we did our chapter on @TypeFamilies@, we wrote an @Add@ family to add
-- two type-level naturals together. If we do a side-by-side comparison of the
-- equivalent "class-based" approach:
type Add :: Nat -> Nat -> Nat -> Constraint
class Add x y z | x y -> z, x z -> y -- , y z -> x -- Boom!

type Add' :: Nat -> Nat -> Nat
type family Add' x y

-- | We see here that there are parallels between classes and type families.
-- Type families produce a result, not a constraint, though we could write
-- @Add' x y ~ z => ...@ to mean the same thing as @Add x y z => ...@. Also,
-- the result of a type family is determined by its inputs - something we can
-- express as a functional dependency!

-- | a. Write the two required instances for the 'Add' class by
-- pattern-matching on the first argument. REMEMBER THAT INSTANCES CAN HAVE
-- CONSTRAINTS, AND THIS IS HOW WE DO RECURSION!
instance Add Z m m
instance Add n m nm => Add (S n) m (S nm)

-- | b. By our analogy, a type family has only "one functional dependency" -
-- all its inputs to its one output. Can we write _more_ functional
-- dependencies for @Add@? Aside from @x y -> z@?

-- | c. We know with addition, @x + y = z@ implies @y + x = z@ and @z - x = y@.
-- This should mean that any pair of these three variables should determine the
-- other! Why couldn't we write all the possible functional dependencies that
-- /should/ make sense?

-- We should want to write @y z -> x@, but this isn't true: both instances
-- would apply to any @y@/@z@ pair where @z@ is an @(S _)@, so there isn't a
-- unique @x@ for all @y@/@z@ combinations!

{- FOUR -}
type Proxy :: k -> Type
data Proxy a = Proxy

-- | As we all know, type signatures are /not/ documentation. This is really
-- because the names of types are far too confusing. To that end, we can give
-- our types friendlier names to make the coding experience less intimidating:
type  IsNamed :: k -> Symbol -> Constraint
class x `IsNamed` label | x -> label, label -> x where
  fromName :: Proxy x -> Proxy label
  fromName _ = Proxy

  toName :: Proxy label -> Proxy x
  toName _ = Proxy

-- | Now we have this class, we can get to work!
instance Int `IsNamed` "Dylan"

instance IO `IsNamed` "Barbara"

instance Float `IsNamed` "Kenneth"


-- | a. In our glorious new utopia, we decide to enact a law that says, "No two
-- types shall have the same name". Similarly, "No type shall have two names".
-- Is there a way to get GHC to help us uphold the law?

-- These lines won't compile:
-- instance String `IsNamed` "Barbara"
-- instance IO `IsNamed` "John"

-- | b. Write the identity function restricted to types named "Kenneth".

idK :: a `IsNamed` "Kenneth" => a -> a
idK = id

-- | c. Can you think of a less-contrived reason why labelling certain types
-- might be useful in real-world code?

-- It might be useful, for example, if we want to produce some sort of
-- language-independent description of data structures. If our description (for
-- example, postgres, or some IDL) refers to "Number", we might want to link
-- that in some way to 'Double'.

{- FIVE -}

-- | Here's a fun little class:
type Omnipresent :: Symbol -> Constraint
class Omnipresent r | -> r -- @-> r@ says "@r@ is unique".

-- | Here's a fun little instance:
instance Omnipresent "Tom!" where

-- | a. Is there a way to enforce that no other instance of this class can ever
-- exist? Do we /need/ variables on the left-hand side of a functional
-- dependency arrow?

-- instance Omnipresent "Joe"

-- | b. Can you think of a time you would ever want this guarantee? Is this
-- "trick" something you can think of a practical reason for doing? Perhaps if
-- we added a method to the class? (Very much an open question).

-- Answer: ?

-- | c. Add another similarly-omnipresent parameter to this type class.

class Omnipresent2 (r :: Symbol) (s :: Symbol) | -> r s
instance Omnipresent2 "Tom!" "Harding!"

{- SIX -}

-- | You knew it was coming, didn't you?
data HList :: [Type] -> Type where
  HNil :: HList '[]
  HCons :: a -> HList as -> HList (a : as)

data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- | a. Write a function (probably in a class) that takes an 'SNat' and an
-- 'HList', and returns the value at the 'SNat''s index within the 'HList'.
type Get :: [Type] -> Nat -> Type -> Constraint
class Get xs n x | xs n -> x where
  get :: SNat n -> HList xs -> x

-- | b. Add the appropriate functional dependency.

instance Get (x:xs) Z x where
  get SZ (HCons x _) = x

instance Get xs n x' => Get (x:xs) (S n) x' where
  get (SS n) (HCons _ xs) = get n xs

-- | c. Write a custom type error!

instance
  TypeError
    ( Text "Index ‘"
        :<>: ShowType n
        :<>: Text "’ out of range"
    ) =>
  Get '[] Z ()
  where
  get = undefined

-- | d. Implement 'take' for the 'HList'.

-- Copied from Chapter 9, with a newly added function dependency:
type HTake :: Nat -> [Type] -> [Type] -> Constraint
class HTake n xs xs' | n xs -> xs' where
  htake :: SNat n -> HList xs -> HList xs'

instance HTake Z xs '[] where
  htake SZ _ = HNil

instance (HTake n xs xs') => HTake (S n) (x : xs) (x : xs') where
  htake (SS n) (x `HCons` xs) = x `HCons` htake n xs

instance HTake n '[] '[] where
  htake _ HNil = HNil

{- SEVEN -}

-- | Recall our variant type:
type Variant :: [Type] -> Type
data Variant xs where
  Here :: x -> Variant (x : xs)
  There :: Variant xs -> Variant (x : xs)
variants :: [Variant [Bool, Int, String]]
variants = [Here True, There (Here 3), There (There (Here "hello"))]
variants' :: [Variant [Bool, Int, String]]
variants' = [inject True, inject @Int 3, inject "hello"]

-- The following is for testing the compiling error message...
-- variants'' :: [Variant [Bool, Int, String]]
-- variants'' = [inject True, inject @Int 3, inject 'A']

type Inject :: Type -> [Type] -> Constraint
class Inject x xs where
  inject :: x -> Variant xs

instance Inject x (x : xs) where
  inject = Here

instance {-# OVERLAPPABLE #-} Inject x xs => Inject x (y : xs) where
  inject = There . inject

instance
  TypeError
    ( Text "Injected type ‘"
        :<>: ShowType x
        :<>: Text "’ not found in the list"
    ) =>
  Inject x '[]
  where
  inject = undefined

-- | Write a function to "project" a value /out of/ a variant. In other words,
-- I would like a function that takes a proxy of a type, a variant containing
-- that type, and returns /either/ a value of that type /or/ the variant
-- /excluding/ that type:
--
-- @
--   project (Proxy :: Proxy Bool) (inject True :: Variant '[Int, String, Bool])
--     === Left Bool :: Either Bool (Variant '[Int, String])
-- @

class Project a as os where
  project :: Proxy a -> Variant as -> Either a (Variant os)

instance Project a (a:as) as where
  project Proxy (Here a) = Left a
  project Proxy (There as) = Right as

instance {-# overlappable #-} Project a as os => Project a (o:as) (o:os) where
  project Proxy (There as) = There <$> project Proxy as
  project Proxy (Here _) = undefined

{- EIGHT -}

-- | It would be nice if I could update a particular index of an HList by
-- providing an index and a (possibly-type-changing) function. For example:
--
-- @
--   update (SS SZ) length (HCons True (HCons "Hello" HNil))
--     === HCons True (HCons 5 HNil)
-- @

-- | Write the type class required to implement this function, along with all
-- its instances and functional dependencies.

{- NINE -}

-- | If you've made it this far, you're more than capable of digesting and
-- understanding some advanced GHC docs! Read the documentation at
-- http://hackage.haskell.org/package/base-4.12.0.0/docs/GHC-Generics.html, and
-- keep going until you hit 'Generic1' - we won't worry about that today.

-- | We can write a little function to get the name of a type as a type-level
-- symbol like so:
class NameOf (x :: Type) (name :: Symbol) | x -> name

instance GNameOf (Rep x) name => NameOf x name

-- | We then have to implement this class that examines the generic tree...
class GNameOf (rep :: Type -> Type) (name :: Symbol) | rep -> name

instance GNameOf (G.D1 ( 'G.MetaData name a b c) d) name

-- | Write a function to get the names of the constructors of a type as a
-- type-level list of symbols.

{- TEN -}

-- | In the standard library, we have a series of @liftA*@ functions, such as
-- 'liftA2', 'liftA3', 'liftA4'... wouldn't it be nice if we just had /one/
-- function called 'lift' that generalised all these?
--
-- liftA1 :: Applicative f => (a -> b) -> f a -> f b
-- liftA1 = lift
--
-- liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
-- liftA2 = lift
--
--
-- liftA3 :: Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
-- liftA3 = lift

-- | Write this function, essentially generalising the f <$> a <*> b <*> c...
-- pattern. It may help to see it as pure f <*> a <*> b <*> c..., and start
-- with a function like this:

-- lift :: (Applicative f, Lift f i o) => i -> o
-- lift = lift' . pure

-- | @class Lift f i o ... where lift' :: ...@ is your job! If you get this
-- right, perhaps with some careful use of @INCOHERENT@, equality constraints,
-- and functional dependencies, you should be able to get some pretty amazing
-- type inference:
--
-- >>> :t lift (++)
-- lift (++) :: Applicative f => f [a] -> f [a] -> f [a]