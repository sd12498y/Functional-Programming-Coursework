-- permanent link: http://goto.ucsd.edu:8090/index.html#?demo=permalink%2F1543858316_9970.hs
import Prelude hiding (reverse, (++), length, foldr, Maybe(..), return, (>>=))
import Language.Haskell.Liquid.Equational

----------------------------------------
-- Define List
----------------------------------------

{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}

data List a = Nil | Cons a (List a)

{-@ measure length               @-}
{-@ length      :: List a -> Nat @-}
length :: List a -> Int
length Nil        = 0
length (Cons x xs) = 1 + length xs

{-@ data List [length] a = Nil | Cons {hd :: a, tl :: List a} @-}

{-@ infix   ++ @-}
{-@ ++      :: List a -> List a -> List a @-}
{-@ reflect ++ @-}
(++) :: List a -> List a -> List a
(++) Nil ys        = ys
(++) (Cons x xs) ys = Cons x (xs ++ ys)

{-@ reverse :: List a -> List a @-}
{-@ reflect reverse @-}
reverse :: List a -> List a
reverse Nil        = Nil
reverse (Cons x xs) = reverse xs ++ (Cons x Nil)

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ v Nil = v
foldr f v (Cons x xs) = f x (foldr f v xs)

----------------------------------------
-- Example
----------------------------------------

{-@ lengthConcat :: xs:List a -> ys:List a -> {length (xs ++ ys) == length xs + length ys} @-}
lengthConcat :: List a -> List a -> Proof
lengthConcat Nil ys
  = length (Nil ++ ys)
  ==. length ys
  ==. 0 + length ys
  ==. length Nil + length ys
  *** QED
lengthConcat (Cons x xs) ys
  = length (Cons x xs ++ ys)
  ==. length (Cons x (xs ++ ys))
  ==. 1 + length (xs ++ ys)
  ==. 1 + length xs + length ys ? lengthConcat xs ys
  ==. length (Cons x xs) + length ys
  *** QED
  
----------------------------------------
-- Question 1
-- uncomment the following line and finish the undefined part
----------------------------------------

{-@ lengthReverse :: xs:List a -> {length (reverse xs) == length xs}@-}
lengthReverse :: List a -> Proof
lengthReverse Nil 
    {- Base case l = [] -}
    = length (reverse Nil)
    {- definition of length -}
    ==. 0
    {- definition of reverse -}
    ==. length Nil
    {- l = [] -}
    *** QED
lengthReverse (Cons x xs)
    {- inductive case: l = (x:xs) -}  
    = length (reverse (Cons x xs))
    {- definition of reverse -}
    ==. length (reverse xs ++ (Cons x Nil))
    {- by lengthConcat -}
    ==. length (reverse xs) + length (Cons x Nil) ? lengthConcat (reverse xs) (Cons x Nil) 
    {- definition of length -}
    ==. length (reverse (xs)) + 1
    {- induction hypothesis -}
    ==. length xs + 1 ? lengthReverse xs
    {- definition of length -}
    ==. length (Cons x xs)
    {- l = (x:xs) -}
    *** QED
  
----------------------------------------
-- Question 2
-- uncomment the following line and finish the undefined part
----------------------------------------

{-@ twiceReverse :: xs:List a -> {reverse (reverse xs) == xs}@-}
twiceReverse :: List a -> Proof
twiceReverse Nil
    {- Base case: xs = [] -}
    = reverse (reverse Nil)
    {- By the definition of reverse -}
    ==. reverse Nil
    {- By the definition of reverse -}
    ==. Nil
    {- xs = [] -}
    ***QED
twiceReverse (Cons x xs)
    {- Inductive case: xs = x:xs -}
    = reverse (reverse (Cons x xs))
    {- By the definition of reverse -}
    ==. reverse (reverse xs ++ (Cons x Nil))
    {- By the definition of reverseConcat -}
    ==. reverse (Cons x Nil) ++ reverse (reverse xs) ? reverseConcat (reverse xs) (Cons x Nil)
    {- By the definition of reverse -}
    ==. reverse Nil ++ (Cons x Nil) ++ reverse (reverse xs)
    {- By the definition of reverse -}
    ==. (Cons x Nil) ++ reverse (reverse xs)
    {- Induction hypothesis -}
    ==. (Cons x Nil) ++ xs ? twiceReverse xs
    {- By the definition of ++ -}
    ==. (Cons x (Nil ++ xs))
    {- By the definition of ++ -}
    ==. (Cons x xs)
    {- xs = x:xs -}
    ***QED

{-@ reverseConcat :: xs:List a -> ys:List a-> {reverse (xs ++ ys) == reverse ys ++ reverse xs}@-}
reverseConcat :: List a -> List a -> Proof
reverseConcat Nil ys
    {- Base case: xs = [] -}
    = reverse (Nil ++ ys)
    {- definition of ++ -}
    ==. reverse ys
    {- definiton of concatNil -}
    ==. reverse ys ++ Nil ? concatNil (reverse ys)
    {- definition of reverse -}
    ==. reverse ys ++ reverse Nil
    {- xs = [] -}
    ***QED
reverseConcat (Cons x xs) ys
    {- Inductive case: xs = x:xs -}
    = reverse ((Cons x xs) ++ ys)
    {- definition of ++ -}
    ==. reverse (Cons x (xs ++ ys))
    {- definition of reverse -}
    ==. reverse (xs ++ ys) ++  (Cons x Nil)
    {- Inuduction hypothesis -}
    ==. reverse ys ++ reverse xs ++ (Cons x Nil) ? reverseConcat xs ys
    {- definition of concatAssoc -}
    ==. reverse ys ++ (reverse xs ++ (Cons x Nil)) ? concatAsso (reverse ys) (reverse xs) (Cons x Nil)
    {- definition of reverse -}
    ==. reverse ys ++ reverse (Cons x xs)
    {- xs = x:xs -}
    ***QED


{-@ concatNil :: xs:List a -> {xs == xs ++ Nil} @-}
concatNil :: List a -> Proof
concatNil Nil
    {- Base case: xs = [] -}
    = Nil
    {- By the definition of ++ -}
    ==. Nil ++ Nil
    {- xs = [] -}
    ***QED
concatNil (Cons x xs)
    {- Inductive case: xs = x:xs -}
    = (Cons x xs)
    {- Induction hypothesis -}
    ==. (Cons x xs) ++ Nil ? concatNil xs
    {- definition of ++ -}
    ==. (Cons x xs) ++ Nil
    ***QED
    
{-@ concatAsso :: xs:List a -> ys:List a -> zs:List a -> {xs ++ ys ++ zs == xs ++ (ys ++ zs)} @-}
concatAsso :: List a -> List a -> List a -> Proof
concatAsso Nil xs ys
    {- Base case: xs = [] -}
    = Nil ++ xs ++ ys
    {- By the definition of ++ -}
    ==. xs ++ ys
    ==. Nil ++ (xs ++ ys)
    {- xs = [] -}
    ***QED
concatAsso (Cons x xs) ys zs
    = (Cons x xs) ++ ys ++ zs
    {- definition of ++ -}
    ==. (Cons x (xs ++ ys)) ++ zs
    {- definition of ++ -}
    ==. Cons x (xs ++ ys ++ zs)
    {- Induction hypothesis -}
    ==. Cons x (xs ++ (ys ++ zs)) ? concatAsso xs ys zs
    {- By the definition of ++ -}
    ==. (Cons x xs) ++ (ys ++ zs)
    ***QED
    
    
    
----------------------------------------
-- Question 3
-- you may or may not need to use beta_application,
-- which essentially states that f x == (\a -> f a) x
----------------------------------------

{-@ beta_application :: bd:b -> f:(a -> {bd':b | bd' == bd}) -> x:a -> {f x == bd } @-}
beta_application :: b -> (a -> b) -> a -> Proof
beta_application bd f x
  = f x ==. bd *** QED


data Maybe a = Nothing | Just a

{-@ reflect return  @-}
return :: a -> Maybe a
return a = Just a

{-@ infix   >>= @-}
{-@ reflect >>= @-}
(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
(>>=) Nothing _ = Nothing
(>>=) (Just a) f = f a

{-@ left_identity :: v:a -> f:(a -> Maybe b) -> {(return v) >>= f == f v} @-}
left_identity :: a -> (a -> Maybe b) -> Proof
left_identity a f
    = (return a) >>= f
    {- definition of return -}
    ==. (Just a) >>= f
    {- definition of >>= -}
    ==. f a
    ***QED

{-@ right_identity :: m:(Maybe a) -> {m >>= return == m} @-}
right_identity :: (Maybe a) -> Proof
right_identity Nothing
    {- case of m = Nothing -}
    = Nothing >>= return
    {- definition of >>= -}
    ==. Nothing
    {- m = Nothing -}
    ***QED
right_identity (Just a)
    {- case of m = Just a -}
    = (Just a) >>= return
    {- definition of >>= -}
    ==. return a
    {- definition of return -}
    ==. Just a
    {- m = Just a -}
    ***QED

{-@ associativity :: m:(Maybe a) -> k:(a -> Maybe b) -> h:(b -> Maybe c) -> {m >>= (\x:a -> k x >>= h) == (m >>= k) >>= h} @-}
associativity :: (Maybe a) -> (a -> Maybe b) -> (b -> Maybe c) -> Proof
associativity Nothing k h
    {- case of m = Nothing -}
    = Nothing >>= (\x -> k x >>= h)
    {- definition of >>= -}
    ==. Nothing
    {- definition of >>= -}
    ==. Nothing >>= h
    {- definition of >>= -}
    ==. (Nothing >>= k) >>= h
    {- m = Nothing -}
    ***QED
associativity (Just a) k h
    {- case of m = Just a -}
    = (Just a) >>= (\x -> k x >>= h)
    {- definition of >>= -}
    ==. (\x -> k x >>= h) a
    {- definition of beta_application-}
    ==. k a >>= h ? beta_application (k a >>= h) (\x -> k x >>= h) a
    {- definition of >>= -}
    ==. (Just a >>= k) >>= h
    {- m = Just a -}
    ***QED
