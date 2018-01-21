{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}

module Cool where

import           Control.Category (Category (..))
import           Data.Either
import           Prelude (Num (..), ($), show)
import qualified Prelude as P

infix 3 <=>
infix 3 ~>

infix 6 .+
infix 7 .*
infixl 1 >>

-- Left ()  = True
-- Right () = False
type Bool = Either () ()

-- the types 'a' and 'b' are isomorphic if we can
-- construct a bijective map between their values.
data a <=> b
  = Iso
  { to   :: a -> b
  , from :: b -> a
  }

instance Category (<=>) where
  id = Iso (\a -> a) (\a -> a)
  (.) bc ab = Iso (to bc . to ab) (from ab . from bc)

(>>) :: Category cat => cat a b -> cat b c -> cat a c
(>>) = P.flip (.)

return :: Category c => c a a
return = id

-- a * b <=> b * a
swapT :: (a,b) <=> (b,a)
swapT = Iso swap swap
  where
    swap (a,b) = (b,a)

-- a + b <=> b + a
swapP :: Either a b <=> Either b a
swapP = Iso swap swap
  where
    swap (Left a ) = Right a
    swap (Right b) = Left b

-- a + (b + c) <=> (a + b) + c
assocP :: Either a (Either b c) <=> Either (Either a b) c
assocP = Iso assocl assocr
  where
    assocl (Left a) = Left (Left a)
    assocl (Right (Left b)) = Left (Right b)
    assocl (Right (Right c)) = Right c

    assocr (Left (Left a)) = Left a
    assocr (Left (Right b)) = Right (Left b)
    assocr (Right c) = Right (Right c)

-- a * (b * c) = (a * b) * c
assocT :: (a,(b,c)) <=> ((a,b),c)
assocT = Iso assocl assocr
  where
    assocl (a, (b,c)) = ((a,b),c)
    assocr ((a,b),c) = (a,(b,c))

-- 1 * a <=> a
unite :: ((),a) <=> a
unite = Iso uniti uniti'
  where
    uniti ((),a) = a
    uniti' a = ((),a)

-- (a + b) * c <=> (a * c) + (b * c)
distrib :: (Either a b, c) <=> Either (a,c) (b,c)
distrib = Iso distrib' factor
  where
    distrib' (Left a, c) = Left (a,c)
    distrib' (Right b, c) = Right (b,c)

    factor (Left (a,c)) = (Left a, c)
    factor (Right (b,c)) = (Right b, c)

-- Given a bijective map between the values of a and b,
-- We can produce a bijective map between the values of b and a
-- (trivial)
sym :: (a <=> b) -> (b <=> a)
sym iso = Iso (from iso) (to iso)

-- Given a bijective map between the values of a and b,
-- and a bijective map between the values of c and d,
-- We can produce a bijective map between (a * c) and (b * d)
(.*) :: (a <=> b) -> (c <=> d) -> ((a,c) <=> (b,d))
(.*) ab cd =
  Iso (\(a,c) -> (to ab a, to cd c))
        (\(b,d) -> (from ab b, from cd d))

-- Given a bijective map between the values of a and b,
-- and a bijective map between the values of c and d,
-- We can produce a bijective map between the values of
-- (a + c) and (b + d)
(.+) :: (a <=> b) -> (c <=> d) -> (Either a c <=> Either b d) 
(.+) ab cd = Iso to' from'
  where
    to' (Left a) = Left (to ab a)
    to' (Right c) = Right (to cd c)
    from' (Left b) = Left (from ab b)
    from' (Right d) = Right (from cd d)

-- Fix :: (* -> *) -> *
newtype Fix f = Fix { unFix :: f (Fix f) }

--data Fix f where
--  unFix :: f (Fix f) -> Fix f

fold :: (f (Fix f)) <=> Fix f
fold = Iso Fix unFix

unfold :: Fix f <=> (f (Fix f))
unfold = Iso unFix Fix

-- If the recursive type is 1 + x, then we can create the initial
-- value left () of type 1 + (1 + x), which leads to the value
-- of 1 + (1 + (1 + x))
type Nat = Fix ((Either) ())

instance P.Show Nat where
  show f = show $ nat2Int f
    where
      nat2Int (Fix (Left ())) = 0
      nat2Int (Fix (Right n)) = 1 + nat2Int n

trace :: forall a b c. (Either a b <=> Either a c) -> (b <=> c)
trace comb = Iso (\b -> loopfwd (to comb (Right b)))
                 (\c -> loopbwd (from comb (Right c)))
  where
    loopfwd :: Either a c -> c
    loopfwd (Left a) = loopfwd (to comb (Left a))
    loopfwd (Right c) = c

    loopbwd :: Either a b -> b
    loopbwd (Left a) = loopbwd (from comb (Left a))
    loopbwd (Right c) = c

not :: Bool <=> Bool
not = swapP

just :: b <=> Either () b
just = Iso Right (\(Right b) -> b)

add1 :: Nat <=> Nat
add1 = just >> fold

sub1 :: Nat <=> Nat
sub1 = sym add1

false :: () <=> Bool
false = just

true :: () <=> Bool
true = just >> not

injectR :: a <=> Either a a
injectR = do
  sym unite
  false .* id
  distrib
  unite .+ unite

zero :: () <=> Nat
zero = trace $ do
  swapP
  fold
  injectR

isZero :: (Nat,Bool) <=> (Nat,Bool)
isZero = do
  sym fold .* id
  distrib
  (id .* not) .+ id
  sym distrib
  fold .* id

move1 :: (Nat,Nat) <=> Either (Nat, Nat) Nat
move1 = do
  sym fold .* id
  distrib
  unite .+ (id .* add1)
  swapP

copoint :: Either a a <=> (a,Bool)
copoint = do
  sym unite .+ sym unite
  sym distrib
  swapT

sw :: (a,(b,c)) <=> (b,(a,c))
sw = do
  assocT
  swapT .* id
  sym assocT

sw2 :: ((a,b),(c,d)) <=> ((a,c),(b,d))
sw2 = do
  sym assocT
  id .* sw
  assocT

iterNat :: (a <=> a) -> ((Nat,a) <=> (Nat,a))
iterNat step = do
  sym unite
  trace $ do
    id
    sym distrib
    (swapP >> fold) .* id
    sw
    (sym fold >> swapP) .* id
    distrib
    (id .* (id .* step) >> sw) .+ id
  unite

isEven :: (Nat,Bool) <=> (Nat,Bool)
isEven = iterNat not

data ListF a b
  = Nil
  | Cons a b

type List a = Fix (ListF a)

instance P.Show a => P.Show (List a) where
  show (Fix Nil) = "[]"
  show (Fix (Cons a b)) = show a P.++ ":" P.++ show b

liste :: List a <=> Either () (a, List a)
liste = Iso to' from'
  where
    to' (Fix Nil) = Left ()
    to' (Fix (Cons a b)) = Right (a,b)
    from' (Left ()) = Fix Nil
    from' (Right (a,b)) = Fix (Cons a b)

cons :: (a,List a) <=> List a
cons = do
  just
  sym liste

swapCbaP :: Either (Either a b) c <=> Either (Either c b) a
swapCbaP = do
  sym assocP
  swapP
  swapP .+ id

diverge :: a <=> b
diverge = trace $ do
  swapP .+ id
  swapCbaP
  sym injectR .+ id
  swapP
  injectR .+ id
  swapCbaP

nil :: () <=> List a
nil = trace $ do
  swapP
  sym liste
  sym unite
  just .* id
  distrib
  (diverge .* id) .+ unite

myList :: () <=> List Bool
myList = do
  nil
  sym unite
  true .* id
  cons
  sym unite
  true .* id
  cons
  sym unite
  false .* id
  cons
  map not

reverse :: List a <=> List a
reverse = withUnit $ iterList id

iterList :: ((a,z) <=> (b,z)) -> ((List a,z) <=> (List b,z))
iterList f = do
  sym unite
  trace $ do
    sym distrib
    (swapP >> sym liste) .* id
    sw
    liste .* id
    distrib
    (.+) id $
      do
        swapT .* id
        sw2
        id .* f
        sw2
    swapP
    (swapT .* id >> sw2) .+ id
  unite

withUnit :: ((a,()) <=> (b,())) -> (a <=> b)
withUnit f = do
  sym unite
  swapT
  f
  sym swapT
  unite

map :: (a <=> b) -> (List a <=> List b)
map f = do
  withUnit . iterList $ f .* id
  reverse

data a ~> b where
  Arr     :: (a <=> b) -> (a ~> b)
  Compose :: (a ~> b) -> (b ~> c) -> (a ~> c)
  First   :: (a ~> b) -> ((a,c) ~> (b,c))
  Left'   :: (a ~> b) -> (Either a c ~> Either b c)
  CreateP :: (() ~> a) -> (() ~> Either a b)
  CreateT :: (() ~> a) -> (() ~> b) -> (() ~> (a,b))
  Erase   :: a ~> ()

instance Category (~>) where
  id  = Arr id
  (.) = P.flip Compose

arr :: (a <=> b) -> (a ~> b)
arr = Arr

erase :: a ~> ()
erase = Erase

first :: (a ~> b) -> ((a,c) ~> (b,c))
first = First

left' :: (a ~> b) -> (Either a c ~> Either b c)
left' = Left'

fstA :: (a,b) ~> a
fstA = do
  arr swapT
  first erase
  arr unite

leftSwap :: ((Either a b), a) <=> ((Either a b), a)
leftSwap = do
  distrib
  swapT .+ id
  sym distrib

leftA :: Create a => a ~> (Either a b)
leftA = do
  arr $ sym unite
  first create
  arr leftSwap
  fstA

join :: (Either a a) ~> a
join = do
  arr $ do
    sym unite .+ sym unite
    sym distrib
    swapT
  fstA

eval :: (a ~> b) -> a -> b
eval (Arr f)       = to f
eval (Compose a b) = eval b P.. eval a
eval (First f)     = \(a,b) -> (eval f a, b)
eval (Left' f)     = let f' (Left a)  = Left $ eval f a
                         f' (Right b) = Right b
                      in f'
eval (CreateT a b) = \_ -> (eval a (), eval b ())
eval (CreateP a)   = Left . eval a
eval Erase         = \_ -> ()

class Create a where
  create :: () ~> a

instance Create () where
  create = id

instance (Create a, Create b) => Create (a,b) where
  create = CreateT create create

instance (Create a) => Create (Either a b) where
  create = CreateP create

class Clone a where
  clone :: a ~> (a,a)

instance Clone () where
  clone = arr $ sym unite

instance (Clone a, Clone b) => Clone (a,b) where
  clone = do
    first clone
    arr swapT
    first clone
    arr $ do
      swapT
      sw2

instance (Create a, Create b, Clone a, Clone b) => Clone (Either a b) where
  clone = do
    left' $ do
      clone
      first leftA
      arr swapT
    arr swapP
    left' $ do
      clone
      first leftA
      arr swapT
    arr $ do
      swapP
      id .+ (id .* swapP)
      sym distrib
