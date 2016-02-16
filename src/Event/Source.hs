{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes                #-}

module Event.Source where

import Control.Applicative
import Control.Exception (throwIO)
import Control.Comonad (Comonad(..))
import Control.Monad.Managed (Managed)
import Data.Functor.Constant (Constant(..))
import Data.Monoid
import Data.Profunctor (Profunctor(..))
import Data.Sequence ((|>))
import Data.Serialize (Serialize(..))
import Pipes (Producer, await, liftIO, yield, (>->))
import Prelude hiding (all, any, length, sum)

import qualified Data.Foldable
import qualified Data.ByteString  as ByteString
import qualified Data.Sequence
import qualified Data.Serialize   as Serialize
import qualified System.Directory

{-| Efficient representation of a left fold that preserves the fold's step
    function, initial accumulator, and extraction function

    This allows the 'Applicative' instance to assemble derived folds that
    traverse a stream only once

    A @('Fold' a b)@ processes elements of type @\'a\'@ and results in a
    value of type @\'b\'@.

    This is almost identical to @"Control.Foldl".'Control.Foldl.Fold'@ except
    with a `Serialize` constraint on the accumulator so that the `Fold`'s
    progress can be persisted.
-}
data Fold a b = forall x . Serialize x => Fold (x -> a -> x) x (x -> b)

instance Functor (Fold a) where
    fmap f (Fold step begin done) = Fold step begin (f . done)
    {-# INLINABLE fmap #-}

instance Profunctor Fold where
    lmap f (Fold step begin done) = Fold step' begin done
      where
        step' x a = step x (f a)
    {-# INLINABLE lmap #-}

    rmap = fmap
    {-# INLINABLE rmap #-}

instance Comonad (Fold a) where
    extract (Fold _ begin done) = done begin
    {-#  INLINABLE extract #-}

    duplicate (Fold step begin done) = Fold step begin (\x -> Fold step x done)
    {-#  INLINABLE duplicate #-}

instance Applicative (Fold a) where
    pure b    = Fold (\() _ -> ()) () (\() -> b)
    {-# INLINABLE pure #-}

    (Fold stepL beginL doneL) <*> (Fold stepR beginR doneR) =
        let step (Pair xL xR) a = Pair (stepL xL a) (stepR xR a)
            begin = Pair beginL beginR
            done (Pair xL xR) = doneL xL (doneR xR)
        in  Fold step begin done
    {-# INLINABLE (<*>) #-}

instance Monoid b => Monoid (Fold a b) where
    mempty = pure mempty
    {-# INLINABLE mempty #-}

    mappend = liftA2 mappend
    {-# INLINABLE mappend #-}

instance Num b => Num (Fold a b) where
    fromInteger = pure . fromInteger
    {-# INLINABLE fromInteger #-}

    negate = fmap negate
    {-# INLINABLE negate #-}

    abs = fmap abs
    {-# INLINABLE abs #-}

    signum = fmap signum
    {-# INLINABLE signum #-}

    (+) = liftA2 (+)
    {-# INLINABLE (+) #-}

    (*) = liftA2 (*)
    {-# INLINABLE (*) #-}

    (-) = liftA2 (-)
    {-# INLINABLE (-) #-}

instance Fractional b => Fractional (Fold a b) where
    fromRational = pure . fromRational
    {-# INLINABLE fromRational #-}

    recip = fmap recip
    {-# INLINABLE recip #-}

    (/) = liftA2 (/)
    {-# INLINABLE (/) #-}

instance Floating b => Floating (Fold a b) where
    pi = pure pi
    {-# INLINABLE pi #-}

    exp = fmap exp
    {-# INLINABLE exp #-}

    sqrt = fmap sqrt
    {-# INLINABLE sqrt #-}

    log = fmap log
    {-# INLINABLE log #-}

    sin = fmap sin
    {-# INLINABLE sin #-}

    tan = fmap tan
    {-# INLINABLE tan #-}

    cos = fmap cos
    {-# INLINABLE cos #-}

    asin = fmap sin
    {-# INLINABLE asin #-}

    atan = fmap atan
    {-# INLINABLE atan #-}

    acos = fmap acos
    {-# INLINABLE acos #-}

    sinh = fmap sinh
    {-# INLINABLE sinh #-}

    tanh = fmap tanh
    {-# INLINABLE tanh #-}

    cosh = fmap cosh
    {-# INLINABLE cosh #-}

    asinh = fmap asinh
    {-# INLINABLE asinh #-}

    atanh = fmap atanh
    {-# INLINABLE atanh #-}

    acosh = fmap acosh
    {-# INLINABLE acosh #-}

    (**) = liftA2 (**)
    {-# INLINABLE (**) #-}

    logBase = liftA2 logBase
    {-# INLINABLE logBase #-}

data Pair a b = Pair !a !b

instance (Serialize a, Serialize b) => Serialize (Pair a b) where
    put (Pair a b) = do
        put a
        put b
    {-# INLiNABLE put #-}

    get = do
        a <- get
        b <- get
        return (Pair a b)
    {-# INLINABLE get #-}

-- | A strict 'Maybe'
data Maybe' a = Just' !a | Nothing'

instance Serialize a => Serialize (Maybe' a) where
    put x = put (lazyMaybe x)
    {-# INLINABLE put #-}

    get = fmap strictMaybe get
    {-# INLINABLE get #-}

-- | Convert 'Maybe'' to 'Maybe'
lazyMaybe :: Maybe' a -> Maybe a
lazyMaybe  Nothing' = Nothing
lazyMaybe (Just' a) = Just a
{-# INLINABLE lazyMaybe #-}

-- | Convert 'Maybe' to 'Maybe''
strictMaybe :: Maybe a -> Maybe' a
strictMaybe  Nothing  = Nothing'
strictMaybe (Just a ) = Just' a
{-# INLINABLE strictMaybe #-}

-- | A strict 'Either'
data Either' a b = Left' !a | Right' !b

instance (Serialize a, Serialize b) => Serialize (Either' a b) where
    put x = put (lazyEither x)
    {-# INLINABLE put #-}

    get = fmap strictEither get
    {-# INLINABLE get #-}

-- | Convert 'Either'' to 'Either'
lazyEither :: Either' a b -> Either a b
lazyEither (Left'  a) = Left a
lazyEither (Right' b) = Right b
{-# INLINABLE lazyEither #-}

-- | Convert 'Either' to 'Either''
strictEither :: Either a b -> Either' a b
strictEither (Left  a) = Left'  a
strictEither (Right b) = Right' b
{-# INLINABLE strictEither #-}

-- | Convert 'Either'' to 'Maybe'
hush :: Either' a b -> Maybe b
hush (Left'  _) = Nothing
hush (Right' b) = Just b
{-# INLINABLE hush #-}

-- | Apply a strict left 'Fold' to a 'Foldable' container
fold :: Foldable f => Fold a b -> f a -> b
fold (Fold step begin done) as = Data.Foldable.foldr cons done as begin
  where
    cons a k x = k $! step x a
{-# INLINE fold #-}

{-| A handler for the upstream input of a `Fold`

    Any lens, traversal, or prism will type-check as a `Handler`
-}
type Handler a b =
    forall x . (b -> Constant (Endo x) b) -> a -> Constant (Endo x) a

{-| @(handles t folder)@ transforms the input of a `Fold` using a lens,
    traversal, or prism:

> handles _1       :: Fold a r -> Fold (a, b) r
> handles _Left    :: Fold a r -> Fold (Either a b) r
> handles traverse :: Traversable t => Fold a r -> Fold (t a) r

>>> fold (handles traverse sum) [[1..5],[6..10]]
55

>>> fold (handles (traverse.traverse) sum) [[Nothing, Just 2, Just 7],[Just 13, Nothing, Just 20]]
42

>>> fold (handles (filtered even) sum) [1,3,5,7,21,21]
42

>>> fold (handles _2 mconcat) [(1,"Hello "),(2,"World"),(3,"!")]
"Hello World!"

> handles id = id
>
> handles (f . g) = handles f . handles g

> handles t (pure r) = pure r
>
> handles t (f <*> x) = handles t f <*> handles t x
-}
handles :: Handler a b -> Fold b r -> Fold a r
handles k (Fold step begin done) = Fold step' begin done
  where
    step' = flip (appEndo . getConstant . k (Constant . Endo . flip step))
{-# INLINABLE handles #-}

-- | Fold all values within a container using 'mappend' and 'mempty'
mconcat :: (Monoid a, Serialize a) => Fold a a
mconcat = Fold mappend mempty id
{-# INLINABLE mconcat #-}

-- | Convert a \"@foldMap@\" to a 'Fold'
foldMap :: (Monoid w, Serialize w) => (a -> w) -> (w -> b) -> Fold a b
foldMap to = Fold (\x a -> mappend x (to a)) mempty
{-# INLINABLE foldMap #-}

{-| Get the first element of a container or return 'Nothing' if the container is
    empty
-}
head :: Serialize a => Fold a (Maybe a)
head = _Fold1 const
{-# INLINABLE head #-}

{-| Get the last element of a container or return 'Nothing' if the container is
    empty
-}
last :: Serialize a => Fold a (Maybe a)
last = _Fold1 (flip const)
{-# INLINABLE last #-}

{-| Get the last element of a container or return a default value if the container
    is empty
-}
lastDef :: Serialize a => a -> Fold a a
lastDef a = Fold (\_ a' -> a') a id
{-# INLINABLE lastDef #-}

-- | Return the last N elements
lastN :: Serialize a => Int -> Fold a [a]
lastN n = Fold step begin done
  where
    step s a = s' |> a
      where
        s' =
            if Data.Sequence.length s < n
            then s
            else Data.Sequence.drop 1 s
    begin = Data.Sequence.empty
    done  = Data.Foldable.toList
{-# INLINABLE lastN #-}

-- | Returns 'True' if the container is empty, 'False' otherwise
null :: Fold a Bool
null = Fold (\_ _ -> False) True id
{-# INLINABLE null #-}

-- | Return the length of the container
length :: Fold a Int
length = genericLength
{- Technically, 'length' is just 'genericLength' specialized to 'Int's.  I keep
   the two separate so that I can later provide an 'Int'-specialized
   implementation of 'length' for performance reasons like "GHC.List" does
   without breaking backwards compatibility.
-}
{-# INLINABLE length #-}

-- | Returns 'True' if all elements are 'True', 'False' otherwise
and :: Fold Bool Bool
and = Fold (&&) True id
{-# INLINABLE and #-}

-- | Returns 'True' if any element is 'True', 'False' otherwise
or :: Fold Bool Bool
or = Fold (||) False id
{-# INLINABLE or #-}

{-| @(all predicate)@ returns 'True' if all elements satisfy the predicate,
    'False' otherwise
-}
all :: (a -> Bool) -> Fold a Bool
all predicate = Fold (\x a -> x && predicate a) True id
{-# INLINABLE all #-}

{-| @(any predicate)@ returns 'True' if any element satisfies the predicate,
    'False' otherwise
-}
any :: (a -> Bool) -> Fold a Bool
any predicate = Fold (\x a -> x || predicate a) False id
{-# INLINABLE any #-}

-- | Computes the sum of all elements
sum :: (Num a, Serialize a) => Fold a a
sum = Fold (+) 0 id
{-# INLINABLE sum #-}

-- | Computes the product all elements
product :: (Num a, Serialize a) => Fold a a
product = Fold (*) 1 id
{-# INLINABLE product #-}

-- | Computes the maximum element
maximum :: (Ord a, Serialize a) => Fold a (Maybe a)
maximum = _Fold1 max
{-# INLINABLE maximum #-}

-- | Computes the minimum element
minimum :: (Ord a, Serialize a) => Fold a (Maybe a)
minimum = _Fold1 min
{-# INLINABLE minimum #-}

{-| @(elem a)@ returns 'True' if the container has an element equal to @a@,
    'False' otherwise
-}
elem :: Eq a => a -> Fold a Bool
elem a = any (a ==)
{-# INLINABLE elem #-}

{-| @(notElem a)@ returns 'False' if the container has an element equal to @a@,
    'True' otherwise
-}
notElem :: Eq a => a -> Fold a Bool
notElem a = all (a /=)
{-# INLINABLE notElem #-}

{-| @(find predicate)@ returns the first element that satisfies the predicate or
    'Nothing' if no element satisfies the predicate
-}
find :: Serialize a => (a -> Bool) -> Fold a (Maybe a)
find predicate = Fold step Nothing' lazyMaybe
  where
    step x a = case x of
        Nothing' -> if predicate a then Just' a else Nothing'
        _        -> x
{-# INLINABLE find #-}

{-| @(index n)@ returns the @n@th element of the container, or 'Nothing' if the
    container has an insufficient number of elements
-}
index :: Serialize a => Int -> Fold a (Maybe a)
index = genericIndex
{-# INLINABLE index #-}

{-| @(elemIndex a)@ returns the index of the first element that equals @a@, or
    'Nothing' if no element matches
-}
elemIndex :: Eq a => a -> Fold a (Maybe Int)
elemIndex a = findIndex (a ==)
{-# INLINABLE elemIndex #-}

{-| @(findIndex predicate)@ returns the index of the first element that
    satisfies the predicate, or 'Nothing' if no element satisfies the predicate
-}
findIndex :: (a -> Bool) -> Fold a (Maybe Int)
findIndex predicate = Fold step (Left' 0) hush
  where
    step x a = case x of
        Left' i ->
            if predicate a
            then Right' i
            else Left' (i + 1)
        _       -> x
{-# INLINABLE findIndex #-}

-- | Like 'length', except with a more general 'Num' return value
genericLength :: (Num b, Serialize b) => Fold a b
genericLength = Fold (\n _ -> n + 1) 0 id
{-# INLINABLE genericLength #-}

-- | Like 'index', except with a more general 'Integral' argument
genericIndex :: (Integral i, Serialize i, Serialize a) => i -> Fold a (Maybe a)
genericIndex i = Fold step (Left' 0) done
  where
    step x a = case x of
        Left'  j -> if i == j then Right' a else Left' (j + 1)
        _        -> x
    done x = case x of
        Left'  _ -> Nothing
        Right' a -> Just a
{-# INLINABLE genericIndex #-}

{-| @_Fold1 step@ returns a new 'Fold' using just a step function that has the
same type for the accumulator and the element. The result type is the
accumulator type wrapped in 'Maybe'. The initial accumulator is retrieved from
the 'Foldable', the result is 'None' for empty containers.
 -}
_Fold1 :: Serialize a => (a -> a -> a) -> Fold a (Maybe a)
_Fold1 step = Fold step_ Nothing' lazyMaybe
  where
    step_ mx a = Just' (case mx of
        Nothing' -> a
        Just' x -> step x a)

{-| 

    The first argument to `eventSource` must obey the following property:

> f n = f 0 >-> Pipes.Prelude.drop n

    In other words, @f n@ must seek to the @n@th element of the event log
-}
eventSource
    :: (Integer -> Managed (Producer a IO r))
    -- ^ Function to seek to an offset in the event log
    -> FilePath
    -- ^ File to persist the `Fold`'s state
    -> Integer
    -- ^ How many events between each checkpoint
    -> Fold a b
    -- ^ Derived result(s) to compute
    -> Managed (Producer b IO r)
    -- ^ Result stream
eventSource acquireEventLog path numEvents userFold =
    case liftA2 (,) genericLength userFold of
        Fold step begin done -> do

        exists <- liftIO (System.Directory.doesFileExist path)
        begin' <- liftIO (do
            if exists
                then do
                    bytes <- ByteString.readFile path
                    case Serialize.decode bytes of
                        Left  str    -> throwIO (userError str)
                        Right begin' -> return begin'
                else return begin )

        let (offset, _) = done begin'

        let scan x = do
                let (n, b) = done x
                if n `rem` numEvents == 0
                    then liftIO (ByteString.writeFile path (Serialize.encode x))
                    else return ()
                yield b
                e <- await
                scan $! step x e

        eventLog <- acquireEventLog offset
        return (eventLog >-> scan begin')
