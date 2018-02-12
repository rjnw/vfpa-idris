

data V : (a : Type) -> (n : Nat) -> Type where
  NIL : V a Z
  (::) : {n : Nat} -> (x : a) -> (xs : V a n) -> V a (S n)

(++) : V a n -> V a m -> V a (n + m)
(++) NIL y = y
(++) (x :: xs) y = x :: (xs ++ y)

total
head : V a (S n) -> a
head (x :: xs) = x

tail : V a n -> V a (pred n)
tail NIL = NIL
tail (x :: xs) = xs

map : (a -> b) -> V a n -> V b n
map f NIL = NIL
map f (x :: xs) = f x :: map f xs

concat : V (V a n) m -> V a (m * n)
concat NIL = NIL
concat (x :: xs) = x ++ (concat xs)

total
nth : (n : Nat) -> V a m -> LT n m -> a
nth Z (x :: _) y = x
nth (S k) (x :: xs) y = nth k xs (fromLteSucc y)

--braun trees
data BraunTr : (a : Type) -> (n : Nat) -> Type where
  Empty : BraunTr a Z
  Node : {n, m : Nat} -> (v : a) -> BraunTr a n -> BraunTr a m -> (Either (n=m) (n=(S m))) -> BraunTr a (S (plus n m))


btil : (n : Nat) -> (m : Nat) -> (S (S (plus m n))) = (S (plus (S n) m))
btil n m = rewrite plusCommutative (S n) m in cong (plusSuccRightSucc m n)

bt_insert : (v : a) -> BraunTr a n -> BraunTr a (S n)
bt_insert x Empty = Node x Empty Empty (Left Refl)
bt_insert x (Node {n=cn} {m=cm} v ln rn p) = rewrite plusCommutative cn cm in case p of
    (Left lp) => let nl = bt_insert x ln in
              rewrite (btil cn cm) in Node v nl rn (Right (cong lp))
    (Right rp) => let nl = bt_insert x rn in Node v nl ln (Left (sym rp))


--binary search tree (specialized for Nats)
-- l=lower bound, u=uppper bound
data BST : (l : Nat) -> (u : Nat) -> Type where
     Leaf : LTE l u -> BST l u
     BNode : (d : Nat) -> BST l' d -> BST d u' -> LTE l l' -> LTE u' u -> BST l u

lte_max : {d : Nat} -> {u : Nat} -> LTE d (maximum d u)
lte_max {d=Z} {u=u} = LTEZero
lte_max {d=(S k)} {u=Z} = lteRefl
lte_max {d=(S k)} {u=(S j)} = LTESucc lte_max


lte_min : {d : Nat} -> {l : Nat} -> LTE (minimum d l) d
lte_min {d=Z} {l=l} = LTEZero
lte_min {d=(S k)} {l=Z} = LTEZero
lte_min {d=(S k)} {l=(S j)} = LTESucc lte_min

data Singleton : {a : Type} -> (x : a) -> Type where
  Keeping : (y : a) -> x = y -> Singleton x

inspect : (x : a) -> Singleton x
inspect x = Keeping x Refl

bst_insert : (d : Nat) -> BST l u -> BST (minimum d l) (maximum d u)
bst_insert d (Leaf p) = BNode d (Leaf lteRefl) (Leaf lteRefl) lte_min lte_max
