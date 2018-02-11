
data L : (a : Type) -> Type where
  NIL : L a
  (::) : (x : a) -> (xs : L a) -> L a

length : {a : Type} -> L a -> Nat
length NIL = 0
length (x :: xs) = succ (length xs)

(++) : {a : Type} -> L a -> L a -> L a
(++) NIL y = y
(++) (x :: xs) y = x :: (xs ++ y)

map : {a, b : Type} -> (a -> b) -> L a -> L b
map f NIL = NIL
map f (x :: xs) = f x :: (map f xs)

filter : {a : Type} -> (a -> Bool) -> L a -> L a
filter f NIL = NIL
filter f (x :: xs) = if f x then x :: (filter f xs) else (filter f xs)

remove : (eq : a -> a -> Bool) -> a -> L a -> L a
remove eq x NIL = NIL
remove eq x (y :: xs) = if eq x y then (remove eq x xs) else y :: (remove eq x xs)

data Mybe : (a : Type) -> Type where
  Just : a -> Mybe a
  Nothing : Mybe a

nth : Nat -> L a -> Mybe a
nth _ NIL = Nothing
nth Z (x :: xs) = Just x
nth (S k) (x :: xs) = nth k xs

sreverse : L a -> L a
sreverse NIL = NIL
sreverse (x :: xs) = (sreverse xs) ++ (x :: NIL)

-- 4.3 proofs on lists
-- length of append is addition of length of each
length_append : (l1, l2 : L a) -> length (l1 ++ l2) = (length l1) + (length l2)
length_append NIL l2 = Refl
length_append (x :: xs) l2 = rewrite (length_append xs l2) in Refl

-- append is associative
assoc_append : (l1, l2, l3 : L a) -> (l1 ++ l2) ++ l3 = l1 ++ (l2 ++l3)
assoc_append NIL l2 l3 = Refl
assoc_append (x :: xs) l2 l3 = rewrite (assoc_append xs l2 l3) in Refl

-- length of filter is less than equal to length of list
length_filter : (p : a -> Bool) -> (l : L a) -> LTE (length (filter p l)) (length l)
length_filter p NIL = LTEZero
length_filter p (x :: xs) with (p x)
                | False = lteSuccRight (length_filter p xs)
                | True = LTESucc (length_filter p xs)

data Singleton : {a : Type} -> (x : a) -> Type where
  Keeping : (y : a) -> x = y -> Singleton x

inspect : (x : a) -> Singleton x
inspect x = Keeping x Refl

-- filter is idempotent
filter_idem : (p : a -> Bool) -> (l : L a) -> (filter p (filter p l)) = (filter p l)
filter_idem p NIL = Refl
filter_idem p (x :: xs) with (inspect (p x))
              | Keeping False pf = rewrite pf in (filter_idem p xs)
              | Keeping True pt = rewrite pt in (rewrite pt in (rewrite (filter_idem p xs) in Refl))

length_distr : (x : L a) ->  (y : a) -> (length (x ++ (y :: NIL))) = S (length x)
length_distr NIL y = Refl
length_distr (x :: xs) y = rewrite (length_distr xs y) in Refl

-- length of reverse is same
length_reverse : (l : L a) -> length (sreverse l) = length l
length_reverse NIL = Refl
length_reverse (x :: xs) = rewrite (length_distr (sreverse xs) x) in rewrite (length_reverse xs) in Refl
