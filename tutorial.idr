
module Tutorial

x : Int
x = 42

-- data Nat = Z | S Nat
-- data List a = Nil | (::) a (List a)

a : Nat
a = plus (S (S Z)) (S (S Z))


-- main : IO ()
-- main = putStrLn ?greeting -- holes

--dependent types

--first class type
isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat

mkSingle : (x : Bool) -> isSingleton x
mkSingle True = 0
mkSingle False = []

-- vector dependent type
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

data Fin : Nat -> Type where
   FZ : Fin (S k)
   FS : Fin k -> Fin (S k)

index : Fin n -> Vect n a -> a
index FZ     (x :: xs) = x
index (FS k) (x :: xs) = index k xs

--implicit arguments
-- index : {a:Type} -> {n:Nat} -> Fin n -> Vect n a -> a

--implicit pattern matching
isEmpty : Vect n a -> Bool
isEmpty {n = Z} _   = True
isEmpty {n = S k} _ = False

data IsElem : a -> Vect n a -> Type where
   Here :  {x:a} ->   {xs:Vect n a} -> IsElem x (x :: xs)
   There : {x,y:a} -> {xs:Vect n a} -> IsElem x xs -> IsElem x (y :: xs)

-- using (x:a, y:a, xs:Vect n a)
--   data IsElem : a -> Vect n a -> Type where
--      Here  : IsElem x (x :: xs)
--      There : IsElem x xs -> IsElem x (y :: xs)


testVec : Vect 4 Int
testVec = 3 :: 5 :: 5 :: 6 :: Nil

-- inVect : IsElem 5 Main.testVec
-- -- inVect = There Here
-- inVect = There (There Here)

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

ifThenElse : Bool -> Lazy a -> Lazy a -> a
ifThenElse True  t e = t
ifThenElse False t e = e

data Sream : Type -> Type where
  (||) : (e : a) -> Sream a -> Sream a

ones : Sream Nat
ones = 1 || ones

--records
record Class where
       constructor ClassInfo
       students : Vect n String
       className : String

-- Interfaces --

-- Functor
-- interface Functor (f : Type -> Type) where
--     map : (m : a -> b) -> f a -> f b

--Applicative
-- infixl 2 <*>

-- interface Functor f => Applicative (f : Type -> Type) where
--     pure  : a -> f a
--     (<*>) : f (a -> b) -> f a -> f b

-- Applicative Maybe where
--   pure = Just
--   Nothing <*> _ = Nothing
--   (Just f) <*> something = fmap f something

-- Monad
-- interface Applicative m => Monad (m : Type -> Type) where
--     (>>=)  : m a -> (a -> m b) -> m b

--namespaces
-- module Foo

-- namespace x
--   test : Int -> Int
--   test x = x * 2

-- namespace y
--   test : String -> String
--   test x = x ++ x

--parameterised blocks
parameters (x : Nat, y : Nat)
  addAll : Nat -> Nat
  addAll z = x + y + z

-- *params> :t addAll
-- addAll : Nat -> Nat -> Nat -> Nat
