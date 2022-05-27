{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Exercises where

import Data.Kind (Constraint, Type)
import Data.Maybe (mapMaybe)
import GHC.TypeLits (Symbol)

{- ONE -}

-- | Let's look at the following type family to build a constraint:

-- Again, Copied from @Relude.Extra.Type.AllHave@:
type AllHave :: (k -> Constraint) -> [k] -> Constraint
type family f `AllHave` xs where
  _ `AllHave` '[] = ()
  f `AllHave` (x : xs) = (f x, f `AllHave` xs)

{- | a. Why does it have to be restricted to 'Type'? Can you make this more
 general?
-}

{- | b. Why does it have to be restricted to 'Constraint'? Can you make this
 more general? Why is this harder?
-}

-- Not really - we need some polymorphic way of "combining" things, probably
-- passed in as another parameter. Because type families can't be
-- partially-applied, this is actually really tricky to do in the general case
-- (at the moment).

{- TWO -}

{- | Sometimes, we're working with a lot of values, and we'd like some way of
 identifying them for the compiler. We could make newtypes, sure, but maybe
 there are loads, and we just don't want the boilerplate. Luckily for us, we
 can introduce this new type:
-}
type TaggedS :: Symbol -> Type -> Type
newtype TaggedS name a = TaggedS {runTaggedS :: a}

{- | 'Tagged' is just like 'Identity', except that it has a type-level string
 attached to it. This means we can write things like this:
-}
x :: TaggedS "Important" Int
x = TaggedS 42

y :: TaggedS "Not so important" Int
y = TaggedS 23

{- | What's more, we can use that tag in function signatures to RESTRICT THE
 INPUT:
-}
f :: TaggedS "Important" Int -> IO () -- ! WHAT A TRICK!
f (TaggedS x) = putStrLn (show x <> " is important!")

{- | a. Symbols are all well and good, but wouldn't it be nicer if we could
 generalise this?
 * A 3rd-party lib is available for this in production: <https://github.com/ekmett/tagged>.
-}
type Tagged :: k -> Type -> Type
newtype Tagged s a = Tagged {unTagged :: a}

-- | b. Can we generalise 'Type'? If so, how? If not, why not?

-- We can't - all runtime values (of which the inner type of 'Tagged' is one)
-- must have kind 'Type'!

{- | c. Often when we use the 'Tagged' type, we prefer a sum type (promoted
 with @DataKinds@) over strings. Why do you think this might be?
-}

-- This allows us to restrict the possible tags that a type may be given to
-- some domain-specific set. Strings could be anything, so it's hard to know
-- when you've covered all your cases.

{- THREE -}

{- | We can use the following to test type-level equivalence.
 (Copied from 'Data.Type.Equality'.)
-}
type (:~:) :: k -> k -> Type
data a :~: b where -- See Note [The equality types story] in GHC.Builtin.Types.Prim
  Refl :: a :~: a

-- | a. What do you think the kind of (:~:) is?

-- Originally:
-- type (:~:) :: Type -> Type -> Type

-- | b. Does @PolyKinds@ make a difference to this kind?

-- Yes. See above.

{- | c. Regardless of your answer to part (b), is this the most general kind we
 could possibly give this constructor? If not (hint: it's not), what more
 general kind could we give it, and how would we tell this to GHC?
-}

-- As a matter of fact, GHC provides a generalized version below:

{- | Kind heterogeneous propositional equality. Like ':~:', @a :~~: b@ is
 inhabited by a terminating value if and only if @a@ is the same type as @b@.
-}
type (:~~:) :: k1 -> k2 -> Type
data a :~~: b where
  HRefl :: a :~~: a

{- FOUR -}

{- | We've talked about singleton types previously, and how they allow us to
 share a value between the value and type levels. Libraries such as
 @singletons@ provide many utilities for working with these types, many of
 which rely on a (type-level) function to get from a kind to its singleton.
 In our toy version of the library, that type family may look like this:
-}
type Sing :: k -> Type
type family Sing x
-- ^ Source: <https://hackage.haskell.org/package/singletons-3.0.1/docs/Data-Singletons.html>

{- | Notice that it's an /open/ type family, thus we define instances for it
 using the @type instance Sing x = y@ syntax.
-}

{- | a. Here's the singleton for the @Bool@ kind. Remembering that the
 singleton for some @x@ of kind @Bool@ is @SBool x@, write a @Sing@ instance
 for the @Bool@ kind. Remember that we can pattern-match on /kinds/ in type
 families - if you're on the right lines, this is a one-liner!
-}
type SBool :: Bool -> Type
data SBool b where
  STrue :: SBool True
  SFalse :: SBool False

type instance Sing x = SBool x

{- | b. Repeat the process for the @Nat@ kind. Again, if you're on the right
 lines, this is very nearly a copy-paste job!
-}
data Nat = Z | S Nat

type SNat :: Nat -> Type
data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

type instance Sing n = SNat n

{- FIVE -}

{- | In dependently-typed programming, we talk about the notion of a "Sigma
 type", or "dependent pair". This is a single-constructor GADT that takes two
 arguments: a singleton for some kind, and some type indexed by the type
 represented by the singleton. Don't panic, let's do an example:
-}

-- | Consider the following GADT to describe a (fixed-length) list of strings:
type Strings :: Nat -> Type
data Strings n where
  SNil :: Strings Z
  (:>) :: String -> Strings n -> Strings (S n)

{- | If we have a working sigma type, we should be able to package a @Strings
 n@ and an @SNat n@ into @Sigma Strings@, existentialising the actual length.
-}
example0 :: [Sigma Strings]
example0 =
  [ Sigma SZ SNil
  , Sigma (SS SZ) ("hi" :> SNil)
  , Sigma (SS (SS SZ)) ("hello" :> ("world" :> SNil))
  ]

{- | a. Write this type's definition: If you run the above example, the
 compiler should do a lot of the work for you...
-}
type Sigma :: (k -> Type) -> Type
data Sigma f where
  Sigma :: Sing n -> f n -> Sigma f

{- | b. Surely, by now, you've guessed this question? Why are we restricting
 ourselves to 'Nat'? Don't we have some more general way to talk about
 singletons? The family of singletons? Any type within the family of
 singletons? Sing it with me! Generalise that type!
-}
example1 :: [Sigma (Vector String)]
example1 =
  [ Sigma SZ VNil
  , Sigma (SS SZ) (VCons "hi" VNil)
  , Sigma (SS (SS SZ)) (VCons "hello" (VCons "world" VNil))
  ]

{- | c. In exercise 5, we wrote a 'filter' function for 'Vector'. Could we
 rewrite this with a sigma type, perhaps?
-}
type Vector :: Type -> Nat -> Type
data Vector a n where -- @n@ and @a@ flipped... Hmm, a clue!
  VNil :: Vector a Z
  VCons :: a -> Vector a n -> Vector a (S n)

sigmaV :: Vector a n -> Sigma (Vector a)
sigmaV VNil = Sigma SZ VNil
sigmaV (VCons x xs) = x `consSV` sigmaV xs

consSV :: a -> Sigma (Vector a) -> Sigma (Vector a)
x `consSV` (Sigma n xs) = Sigma (SS n) (VCons x xs)

filterV :: (a -> Bool) -> Sigma (Vector a) -> Sigma (Vector a)
_ `filterV` vNil@(Sigma SZ VNil) = vNil
f `filterV` Sigma (SS n) (VCons x xs) =
  let tail = f `filterV` Sigma n xs
   in if f x then consSV x tail else tail

{- SIX -}

{- | Our sigma type is actually very useful. Let's imagine we're looking at
 a communication protocol over some network, and we label our packets as
 @Client@ or @Server@:
-}
data Label = Client | Server

-- | Client data and server data are different, however:
data ClientData = ClientData
  { name :: String
  , favoriteInt :: Int
  }

data ServerData = ServerData
  { favoriteBool :: Bool
  , complimentaryUnit :: ()
  }

{- | a. Write a GADT indexed by the label that holds /either/ client data or
 server data.
-}
type Communication :: Label -> Type
data Communication l where
  ClientCommunication :: ClientData -> Communication Client
  ServerCommunication :: ServerData -> Communication Server

-- | b. Write a singleton for 'Label'.
type SLabel :: Label -> Type
data SLabel l where
  SClient :: SLabel Client
  SServer :: SLabel Server

type instance Sing l = SLabel l

{- | c. Magically, we can now group together blocks of data with differing
 labels using @Sigma Communication@, and then pattern-match on the 'Sigma'
 constructor to find out which packet we have! Try it:
-}
serverLog :: [Sigma Communication] -> [ServerData]
serverLog = mapMaybe \case
  Sigma SServer (ServerCommunication d) -> Just d
  _ -> Nothing

{- | d. Arguably, in this case, the Sigma type is overkill; what could we have
 done, perhaps using methods from previous chapters, to "hide" the label
 until we pattern-matched?
-}

-- Just /not/ used a type index! Sigma types become much more useful when we're
-- dealing with extensible sets of data - perhaps something like:
--
-- @
--   data Communication (label :: Label) where
--     Packet :: DataFor label -> Communication label
-- @
--
-- For some @DataFor@ type family that tells you what the packet should look
-- like. In this case, we don't need separate constructors for each label, but
-- we lose the ability to pattern-match without knowing the type.
