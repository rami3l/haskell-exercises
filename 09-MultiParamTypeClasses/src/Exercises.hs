{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Exercises where

import Data.Kind (Constraint, Type)
import Data.Map (Map)
import Data.Proxy (Proxy (..))
import Data.Type.Bool (type (&&))
import Data.Type.Equality (type (==))
import GHC.TypeLits (ErrorMessage (..), TypeError)

{- ONE -}

-- | Consider the following types:
newtype MyInt = MyInt Int

newtype YourInt = YourInt Int

{- | As Haskell programmers, we love newtypes, so it would be super useful if
 we could define a class that relates a newtype to the type it wraps, while
 also giving us functions to get between them (we can call them 'wrap' and
 'unwrap').
-}

{- | a. Write the class!
 Source: <https://hackage.haskell.org/package/newtype-0.2.2.0/docs/Control-Newtype.html#t:Newtype>
-}
type Newtype :: Type -> Type -> Constraint
class Newtype new old | new -> old where
  wrap :: old -> new
  unwrap :: new -> old

-- | b. Write instances for 'MyInt' and 'YourInt'.
instance Newtype MyInt Int where
  wrap = MyInt
  unwrap (MyInt n) = n

instance Newtype YourInt Int where
  wrap = YourInt
  unwrap (YourInt n) = n

{- | c. Write a function that adds together two values of the same type,
 providing that the type is a newtype around some type with a 'Num' instance.
-}
addW :: (Num n, Newtype w n) => w -> w -> w
addW w w' = wrap $ unwrap w + unwrap w'

{- | d. We actually don't need @MultiParamTypeClasses@ for this if we use
 @TypeFamilies@. Look at the section on associated type instances here:
 https://wiki.haskell.org/GHC/Type_families#Associated_type_instances_2 -
 rewrite the class using an associated type, @Old@, to indicate the
 "unwrapped" type. What are the signatures of 'wrap' and 'unwrap'?
-}
type Newtype' :: Type -> Constraint
class Newtype' new where
  -- ! Similar to Rust trait's associated type (@trait C { type T; }@),
  -- for any implementer I of C, since it can implement C exactly once,
  -- there's a unique associated type T, thus a TYPE-LEVEL FUNCTION has been
  -- established from I to T. Below is actually a type family:
  type Old (new :: Type) :: Type

  wrap' :: Old new -> new
  unwrap' :: new -> Old new

instance Newtype' MyInt where
  -- The full syntax actually starts with @type instance@:
  type Old MyInt = Int
  wrap' = MyInt
  unwrap' (MyInt n) = n

instance Newtype' YourInt where
  type Old YourInt = Int
  wrap' = YourInt
  unwrap' (YourInt n) = n

{- TWO -}

{- | Who says we have to limit ourselves to /types/ for our parameters? Let's
 look at the definition of 'traverse':
-}
traverse1 :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
traverse1 = traverse

{- | This is all very well, but we often don't need @f@ to be an 'Applicative'.
 For example, let's look at the good ol' 'Identity' type:
-}
newtype Identity a = Identity a deriving (Functor) -- LANGUAGE DeriveFunctor

instance Foldable Identity where
  foldMap f (Identity x) = f x

instance Traversable Identity where
  traverse f (Identity x) = Identity <$> f x

{- | We can see that, in the @Traversable@ instance, we don't actually use
 @pure@ /or/ @(<*>)@ - we only use @<$>@! It would be nice if we could have a
 better @Traversable@ class that takes both the @t@ type /and/ the constraint
 we want on the @f@...
-}

{- | a. Write that little dazzler! What error do we get from GHC? What
 extension does it suggest to fix this?
-}
type Wanderable :: ((Type -> Type) -> Constraint) -> (Type -> Type) -> Constraint
class Wanderable c t | t -> c where
  wander :: c f => (a -> f b) -> t a -> f (t b)
-- ^ @{\-# LANGUAGE AllowAmbiguousTypes #-\}@ required.

-- | b. Write a 'Wanderable' instance for 'Identity'.
instance Wanderable Functor Identity where
  f `wander` (Identity x) = Identity <$> f x

{- | c. Write 'Wanderable' instances for 'Maybe', '[]', and 'Proxy', noting the
 differing constraints required on the @f@ type. '[]' might not work so well,
 and we'll look at /why/ in the next part of this question!
-}
instance Wanderable Applicative Maybe where
  _ `wander` Nothing = pure Nothing
  f `wander` (Just x) = Just <$> f x

instance Wanderable Applicative [] where
  _ `wander` [] = pure []
  {- @Could not deduce c0 f@ - the problem here is that, in the recursive case,
  we can't figure out which @Wanderable@ instance we want for the tail. To
  /us/, this seems strange - we just want the list version! However, we
  haven't yet told GHC that there's only ever going to be one @Wanderable@
  instance for @[]@, so it will complain.
  Thus, @TypeApplications@ must be used to indicate that we just want this instance:
  <https://gitlab.haskell.org/ghc/ghc/-/wikis/type-application> -}
  f `wander` (x : xs) = (:) <$> f x <*> wander @Applicative @[] f xs

instance Wanderable Applicative Proxy where
  _ `wander` _ = pure Proxy

{- | d. Assuming you turned on the extension suggested by GHC, why does the
 following produce an error? Using only the extensions we've seen so far, how
 could we solve this, perhaps in a way that involves another parameter to the
 'wander' function? A parameter whose type could be annotated? (Don't worry -
 we'll see in later chapters that there are neater solutions to this
 problem!)
-}
test = wander Just [1, 2, 3]
{- ^ To disambiguate, @instance Wanderable Applicative []@ can be changed to @instance c ~ Applicative => Wanderable c []@.
  However, a better solution is to use @FunctionalDependencies@.
  ...or, if multiple possible instances for @Wanderable _ []@ is desired, @TypeApplication@ can be used:
-}

-- test = wander @Applicative Just [1, 2, 3]

{- THREE -}

data Nat = Z | S Nat

data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

{- | In the @DataKinds@ chapter, we wrote the 'SmallerThan' data type, which
 we'll call 'Fin' from now on:
 Source: <https://agda.github.io/agda-stdlib/Data.Fin.Base.html#1203>
-}

-- | Finite numbers: @[0..n-1]@.
data Fin :: Nat -> Type where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

{- | We can write a class to take an 'SNat' to a 'Fin' using
 @MultiParamTypeClasses@. We can even use @TypeOperators@ to give our class a
 more intuitive name:
-}
type (<) :: Nat -> Nat -> Constraint
class x < y where
  convert :: SNat x -> Fin y
  coconvert :: Fin y -> Maybe (SNat x)

-- | a. Write the instance that says @Z@ is smaller than @S n@ for /any/ @n@.
instance Z < S n where
  convert SZ = FZ

  coconvert FZ = Just SZ
  coconvert _ = Nothing

{- | b. Write an instance that says, if @x@ is smaller than @y@, then @S x@ is
 smaller than @S y@.
-}
instance (x < y) => S x < S y where
  convert (SS n) = FS $ convert n

  coconvert FZ = Nothing
  coconvert (FS n) = SS <$> coconvert n

{- | c. Write the inverse function for the class definition and its two
 instances.
-}

{- FOUR -}

{- | In a couple places, we've seen the @(~)@ (or "equality") constraint being
 used. Essentially, we can think of it as a two-parameter typeclass with one
 instance.
-}

-- | a. Write that typeclass!
class TypeEquals (x :: Type) (y :: Type) where
  to :: x -> y
  from :: y -> x

-- | b. Write that instance!
instance x ~ y => TypeEquals x y where
  from = id
  to = id

{- | c. When GHC sees @x ~ y@, it can apply anything it knows about @x@ to @y@,
 and vice versa. We don't have the same luxury with /our/ class, however –
 because we can't convince the compiler that only one instance will ever
 exist, it can't assume that we want the instance we've just written. No
 matter, though - we can just add two functions (@x -> y@ and @y -> x@) to
 our class to convert between the types. Write them, and don't overthink!
-}

{- | d. GHC can see @x ~ y@ and @y ~ z@, then deduce that @x ~ z@. Can we do
 the same? Perhaps with a second instance? Which pragma(s) do we need and
 why? Can we even solve this?
-}

-- Duplicate instance declarations: @instance (x ~ y) => TypeEquals x y@
-- instance (TypeEquals x y, TypeEquals y z) => TypeEquals x z where
--   from = id
--   to = id

{- FIVE -}

-- | It wouldn't be a proper chapter without an @HList@, would it?
type HList :: [Type] -> Type
data HList xs where
  HNil :: HList '[]
  HCons :: a -> HList as -> HList (a : as)

-- In fact, you know what? You can definitely write an HList by now – I'll
-- just put my feet up and wait here until you're done!

{- | Consider the following class for taking the given number of elements from
 the front of an HList:
-}
type HTake :: Nat -> [Type] -> [Type] -> Constraint
class HTake n xs xs' where
  htake :: SNat n -> HList xs -> HList xs'

-- | a. Write an instance for taking 0 elements.
instance HTake Z xs '[] where
  htake SZ _ = HNil

{- | b. Write an instance for taking a non-zero number. You "may" need a
 constraint on this instance.
-}
instance (HTake n xs xs') => HTake (S n) (x : xs) (x : xs') where
  htake (SS n) (x `HCons` xs) = x `HCons` htake n xs

-- | c. What case have we forgotten? How might we handle it?
instance HTake n '[] '[] where
  htake _ HNil = HNil

{- SIX -}

-- | We could also imagine a type class to "pluck" types out of @HList@:
type Pluck :: Type -> [Type] -> Constraint
class Pluck x xs where
  pluck :: HList xs -> x

-- | a. Write an instance for when the head of @xs@ is equal to @x@.
instance Pluck x (x : xs) where
  pluck (HCons x _) = x

-- | b. Write an instance for when the head /isn't/ equal to @x@.
instance {-# OVERLAPPABLE #-} Pluck x xs => Pluck x (y : xs) where
  pluck (HCons y xs) = pluck xs

{- | c. Using [the documentation for user-defined type
 errors](http://hackage.haskell.org/package/base-4.11.1.0/docs/GHC-TypeLits.html#g:4)
 as a guide, write a custom error message to show when you've recursed
 through the entire @xs@ list (or started with an empty @HList@) and haven't
 found the type you're trying to find.
-}
instance
  TypeError
    ( Text "Plucked type ‘"
        :<>: ShowType a
        :<>: Text "’ not found in the list"
    ) =>
  Pluck a '[]
  where
  pluck = undefined

{- | d. Making any changes required for your particular HList syntax, why
 doesn't the following work? Hint: try running @:t 3@ in GHCi.
-}
mystery :: Int
-- Answer: Integer literals are generic...
-- mystery = pluck (HCons "world" (HCons 3 HNil))
mystery = pluck (HCons "world" (HCons @Int 3 HNil))

{- SEVEN -}

{- | A variant is similar to an 'Either', but generalized to any non-zero
 number of parameters. Typically, we define it with two parameters: @Here@
 and @There@. These tell us which "position" our value inhabits:
-}
variants :: [Variant [Bool, Int, String]]
variants = [Here True, There (Here 3), There (There (Here "hello"))]

-- | a. Write the 'Variant' type to make the above example compile.
type Variant :: [Type] -> Type
data Variant xs where
  Here :: x -> Variant (x : xs)
  There :: Variant xs -> Variant (x : xs)

{- | b. The example is /fine/, but there's a lot of 'Here'/'There' boilerplate.
 Wouldn't it be nice if we had a function that takes a type, and then returns
 you the value in the right position? Write it! If it works, the following
 should compile: @[inject True, inject (3 :: Int), inject "hello"]@.
-}
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

{- | c. Why did we have to annotate the 3? This is getting frustrating... do
 you have any (not necessarily good) ideas on how we /could/ solve it?
-}

{- EIGHT -}

{- | As engineers, we are wont to over-think day-to-day problems in order to
 justify our existence to scrum masters. As such, we are compelled to visit
 our friendly neighbourhood angel investor with a new idea: given the weather
 and rough temperature, our web2.0, blockchain-ready app - chil.ly - will
 tell you whether or not you need a coat. Let's start by defining our inputs:
-}
data Weather = Sunny | Raining

data Temperature = Hot | Cold

-- ... and some singletons, why not?

type SWeather :: Weather -> Type
data SWeather w where
  SSunny :: SWeather Sunny
  SRaining :: SWeather Raining

type STemperature :: Temperature -> Type
data STemperature t where
  SHot :: STemperature Hot
  SCold :: STemperature Cold

{- | Now, our app is going to be ready-for-scale, B2B, and proven with zero
 knowledge, so we want type safety /at the core/. Naturally, we've defined
 the relationship between the two domains as a type class.
-}
type Coat :: Weather -> Temperature -> Constraint
class Coat a b where
  doINeedACoat :: SWeather a -> STemperature b -> Bool

{- | It's early days, and we're just building an MVP, but there are some rules
 that /everyone/ knows, so they should be safe enough!
-}

-- No one needs a coat when it's sunny!
instance {-# INCOHERENT #-} Coat Sunny b where doINeedACoat _ _ = False

-- It's freezing out there - put a coat on!
instance Coat a Cold where doINeedACoat _ _ = True

{- | Several months pass, and your app is used by billions of people around the
 world. All of a sudden, your engineers encounter a strange error:
-}
testCoat :: Bool
testCoat = doINeedACoat SSunny SCold

{- | Clearly, our data scientists never thought of a day that could
 simultaneously be sunny /and/ cold. After months of board meetings, a
 decision is made: you /should/ wear a coat on such a day. Thus, the
 __second__ rule is a higher priority.
-}

{- | a. Uncomment the above, and add OVERLAPPING and/or OVERLAPPABLE pragmas
 to prioritize the second rule. Why didn't that work? Which step of the
 instance resolution process is causing the failure?
-}

-- Answer: To GHC, the two instances are equally SPECIFIC, so OVERLAP* doesn't work.

{- | b. Consulting the instance resolution steps, which pragma /could/ we use
 to solve this problem? Fix the problem accordingly.
-}

{- | c. In spite of its scary name, can we verify that our use of it /is/
 undeserving of the first two letters of its name?
-}

-- There's only one INCOHERENT instance, so the choice will never be non-deterministic.

{- NINE -}

{- | The 'Show' typeclass has two instances with which we're probably quite
 familiar:
-}

-- instance Show a => Show [a]
-- instance           Show String

-- | a. Are these in conflict? When?

-- Answer: No, because String doesn't implement `Show`.
-- In fact, the printing of a `String` is handled in the `showList` method of `Char`.

{- | b. Let's say we want to define an instance for any @f a@ where the @f@ is
 'Foldable', by converting our type to a list and then showing that. Is there
 a pragma we can add to the first 'Show' instance above so as to preserve
 current behavior? Would we need /more/ pragmas than this?
-}

-- OVERLAPPABLE would do it for the previous case. In our specific contrived case,
-- we might be better off adding OVERLAPS to all of them, so we simply pick the
-- most specific instance available at the time.

{- | c. Somewhat confusingly, we've now introduced incoherence: depending on
 whether or not I've imported this module, 'show' will behave in different
 ways. Your colleague suggests that your use of pragmas is the root issue
 here, but they are missing the bigger issue; what have we done? How could we
 have avoided it?
-}

-- @f a@ is almost certainly an orphan instance! We'd have been better off
-- creating something like @newtype ShowFoldable f a = SF (f a)@ and writing a
-- Show instance for that.

{- TEN -}

-- | Let's imagine we have some types in our codebase:
newtype UserId = UserId Int

data User = User
  { uid :: UserId
  , knownAs :: String
  }

newtype CommentId = CommentId Int

data Comment = Comment
  { uid :: CommentId
  , author :: UserId
  , text :: String
  }

data Status = Blocked | Deleted

{- | In order to better facilitate mobile devices, we now want to introduce
 caching. I start work, and eventually slide a pull request into your DMs:
-}
class UserCache where
  storeUser :: User -> Map UserId User -> Map UserId User
  loadUser :: Map UserId User -> UserId -> Either Status User

class CommentCache where
  storeComment :: Comment -> Map CommentId Comment -> Map CommentId Comment
  loadComment :: Map CommentId Comment -> CommentId -> Maybe Comment

{- | "This is silly", you exclaim. "These classes only differ in three ways! We
 could write this as a multi-parameter type class!"
-}

{- | a. What are those three ways? Could we turn them into parameters to a
 typeclass? Do it!
-}
type Cache :: Type -> Type -> (Type -> Type) -> Constraint
class Cache item uid f | item -> uid f where
  store :: item -> Map uid item -> Map uid item
  load :: Map uid item -> uid -> f uid

{- | b. Write instances for 'User' and 'Comment', and feel free to implement
 them as 'undefined' or 'error'. Now, before uncommenting the following, can
 you see what will go wrong? (If you don't see an error, try to call it in
 GHCi...)
-}
instance Cache User UserId (Either Status) where
  store = undefined
  load = undefined

instance Cache Comment CommentId Maybe where
  store = undefined
  load = undefined

oops cache = load cache (UserId (123 :: Int))

{- | c. Do we know of a sneaky trick that would allow us to fix this? Possibly
 involving constraints? Try!
-}

-- Oops, @FunctionalDependencies@ required.
