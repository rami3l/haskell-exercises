{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Exercises where

import Data.Bifunctor (Bifunctor (first))
import Data.Function ((&))
import Data.Tuple (swap)

{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where count :: a -> Int

instance Countable Int where count = id

instance Countable [a] where count = length

instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.
data CountableList where
  CountableNil :: CountableList
  CountableCons :: Countable a => a -> CountableList -> CountableList

-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.
countList :: CountableList -> Int
countList CountableNil = 0
countList (CountableCons car cdr) = count car + countList cdr

-- | c. Write a function that removes all elements whose count is 0.
dropZero :: CountableList -> CountableList
dropZero CountableNil = CountableNil
dropZero (CountableCons car cdr) =
  let cdr' = dropZero cdr
   in if count car == 0 then cdr' else car `CountableCons` cdr'

-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?
filterInts :: CountableList -> CountableList
filterInts = error "Impossible!"

{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.
data AnyList where
  AnyNil :: AnyList
  AnyCons :: a -> AnyList -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?
reverseAnyList :: AnyList -> AnyList
reverseAnyList = go AnyNil
  where
    go l AnyNil = l
    go l (AnyCons rcar rcdr) = go (rcar `AnyCons` l) rcdr

-- filterAnyList :: (a -> Bool) -> AnyList -> AnyList
-- filterAnyList _ AnyNil = AnyNil
-- filterAnyList f (AnyCons car cdr) =
--   let cdr' = filterAnyList f cdr
--    in if f car then car `AnyCons` cdr' else cdr'
-- This won't typecheck, since @a@ in @a -> Bool@ is different from the existential @a@ in the @AnyList@ decl.

lengthAnyList :: AnyList -> Int
lengthAnyList AnyNil = 0
lengthAnyList (AnyCons _ cdr) = 1 + lengthAnyList cdr

-- foldAnyList :: Monoid m => AnyList -> m
-- foldAnyList (AnyCons car cdr) = car <> foldAnyList cdr

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList AnyNil = True
isEmptyAnyList _ = False

instance Show AnyList where
  show AnyNil = "Nil"
  show (AnyCons car cdr) = "Car : " ++ show cdr

{- THREE -}

-- | Consider the following GADT:
data TransformableTo output where
  TransformWith ::
    (input -> output) ->
    input ->
    TransformableTo output

-- | ... and the following values of this GADT:
transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it?
unTransform :: TransformableTo o -> o
unTransform (TransformWith f i) = f i

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check?
instance Eq o => Eq (TransformableTo o) where
  t == t' = unTransform t == unTransform t'

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?
instance Functor TransformableTo where
  fmap f = TransformWith f . unTransform

instance Show o => Show (TransformableTo o) where
  show t = "TransformableTo " ++ show (unTransform t)

{- FOUR -}

-- | Here's another GADT:
data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?
unEqPair :: EqPair -> Bool
unEqPair (EqPair a a') = a' == a

-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)
data EqPair' a where
  EqPair' :: Eq a => a -> a -> EqPair' a

deriving instance Show a => Show (EqPair' a)

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?
data EqPair'' a = Eq a => EqPair'' a a

deriving instance Show a => Show (EqPair'' a)

{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.
data MysteryBox a where
  EmptyBox :: MysteryBox ()
  IntBox :: Int -> MysteryBox () -> MysteryBox Int
  StringBox :: String -> MysteryBox Int -> MysteryBox String
  BoolBox :: Bool -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.
getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:
getInt' :: MysteryBox String -> Int
getInt' (StringBox _ (IntBox n _)) = n

-- | b. Write the following function. Again, don't overthink it!
countLayers :: MysteryBox a -> Int
countLayers EmptyBox = 0
countLayers (IntBox _ mb) = 1 + countLayers mb
countLayers (StringBox _ mb) = 1 + countLayers mb
countLayers (BoolBox _ mb) = 1 + countLayers mb

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?
data Layer a b where
  Int' :: Layer () Int
  String' :: Layer Int String
  Bool' :: Layer String Bool

unBox :: Layer a b -> MysteryBox b -> MysteryBox a
unBox Int' (IntBox _ mb) = mb
unBox String' (StringBox _ mb) = mb
unBox Bool' (BoolBox _ mb) = mb

{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:
data HList a where
  HNil :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!
head :: HList (a, b) -> a
head (HCons head _) = head

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?
patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe = error "Impossible!"

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?

{- SEVEN -}

-- | Here are two data types that may help:
-- data Empty -- Replaced with ()
-- data Branch left center right -- Replaced with (l, c, r)

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.
data HTree a where
  HEmpty :: HTree ()
  HBranch :: HTree l -> c -> HTree r -> HTree (l, c, r)

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?
removeLeftChild :: HTree (l, c, r) -> HTree ((), c, r)
removeLeftChild (HBranch _ c r) = HBranch HEmpty c r

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!
instance Eq (HTree ()) where
  _ == _ = True

instance (Eq (HTree l), Eq c, Eq (HTree r)) => Eq (HTree (l, c, r)) where
  HBranch l c r == HBranch l' c' r' = l == l' && c == c' && r == r'

{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @
data AlternatingList a b where
  ANil :: AlternatingList a b
  ACons :: a -> AlternatingList b a -> AlternatingList a b

deriving instance (Show a, Show b) => Show (AlternatingList a b)

alternatingList1 :: AlternatingList Bool Int
alternatingList1 = ACons True (ACons 1 (ACons False (ACons 2 ANil)))

-- | b. Implement the following functions.
getFirsts :: AlternatingList a b -> [a]
getFirsts ANil = []
getFirsts (ACons car cdr) = car : getSeconds cdr

getSeconds :: AlternatingList a b -> [b]
getSeconds ANil = []
getSeconds (ACons car cdr) = getFirsts cdr

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.
foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues ANil = (mempty, mempty)
foldValues (ACons car cdr) = let (b, a) = foldValues cdr in (car <> a, b)

{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.
data Expr a where
  Equals :: Expr Int -> Expr Int -> Expr Bool
  Add :: Expr Int -> Expr Int -> Expr Int
  If :: Expr Bool -> Expr a -> Expr a -> Expr a
  IntValue :: Int -> Expr Int
  BoolValue :: Bool -> Expr Bool

deriving instance Show a => Show (Expr a)

-- | a. Implement the following function and marvel at the typechecker:
eval :: Expr a -> a
eval (Equals l r) = eval l == eval r
eval (Add l r) = eval l + eval r
eval (If p then' else') = eval $ if eval p then then' else else'
eval (IntValue n) = n
eval (BoolValue b) = b

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?
data DirtyExpr
  = DirtyEquals DirtyExpr DirtyExpr
  | DirtyAdd DirtyExpr DirtyExpr
  | DirtyIf DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue Int
  | DirtyBoolValue Bool

{-
parseBool :: DirtyExpr -> Maybe (Expr Bool)
parseBool (DirtyEquals l r) = Equals <$> parseInt l <*> parseInt r
parseBool (DirtyAdd _ _) = Nothing
parseBool (DirtyIf p then' else') = If <$> parseBool p <*> parseBool then' <*> parseBool else'
parseBool (DirtyIntValue n) = Nothing
parseBool (DirtyBoolValue b) = Just $ BoolValue b

parseInt :: DirtyExpr -> Maybe (Expr Int)
parseInt (DirtyEquals _ _) = Nothing
parseInt (DirtyAdd l r) = Add <$> parseInt l <*> parseInt r
parseInt (DirtyIf p then' else') = If <$> parseBool p <*> parseInt then' <*> parseInt else'
parseInt (DirtyIntValue n) = Just $ IntValue n
parseInt (DirtyBoolValue b) = Nothing
-}

data Typed where
  IntType :: Expr Int -> Typed
  BoolType :: Expr Bool -> Typed

parse :: DirtyExpr -> Maybe Typed
parse (DirtyEquals l r) = case (parse l, parse r) of
  (Just (IntType l), Just (IntType r)) -> Just . BoolType $ l `Equals` r
  _ -> Nothing
parse (DirtyAdd l r) = case (parse l, parse r) of
  (Just (IntType l), Just (IntType r)) -> Just . IntType $ l `Add` r
  _ -> Nothing
parse (DirtyIf p then' else') = case (parse p, parse then', parse else') of
  (Just (BoolType p), Just (IntType then'), Just (IntType else')) -> Just . IntType $ If p then' else'
  (Just (BoolType p), Just (BoolType then'), Just (BoolType else')) -> Just . BoolType $ If p then' else'
  _ -> Nothing
parse (DirtyIntValue n) = Just . IntType . IntValue $ n
parse (DirtyBoolValue b) = Just . BoolType . BoolValue $ b

parseInt :: DirtyExpr -> Maybe (Expr Int)
parseInt exp = case parse exp of
  Just (IntType i) -> Just i
  _ -> Nothing

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?

-- We can steal functions from Haskell to achieve this sort of thing. When we
-- do so, it's called a Higher-Order Abstract Syntax (or HOAS for short). This
-- means we end up with a pretty little thing like:

data MoreExpr a where
  Function :: (a -> MoreExpr b) -> MoreExpr (a -> b)
  Apply :: MoreExpr (a -> b) -> MoreExpr a -> MoreExpr b

{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.
data TypeAlignedList a b where
  TypeAlignedNil :: TypeAlignedList a a
  TypeAlignedCons :: (a -> b) -> TypeAlignedList b c -> TypeAlignedList a c

-- | b. Which types are existential?

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.
composeTALs :: TypeAlignedList a b -> TypeAlignedList b c -> TypeAlignedList a c
composeTALs TypeAlignedNil l = l
composeTALs (TypeAlignedCons fau lub) lbc = TypeAlignedCons fau $ lub `composeTALs` lbc