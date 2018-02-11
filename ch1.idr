

data B : Type where
  T : B
  F : B

not : B -> B
not T = F
not F = T

(&&) : B -> B -> B
T && b = b
F && b = F

a : B
a = T && T

(||) : B -> B -> B
T || b = T
F || b = b

nntt : not (not T) = T
nntt = Refl

ite : B -> a -> a -> a
ite T y z = y
ite F y z = z

nelim : (b : B) -> not (not b) = b
nelim T = Refl
nelim F = Refl

same_and : {b : B} -> b && b = b
same_and {b = T} = Refl
same_and {b = F} = Refl

total
or_forall : {b1, b2 : B} -> b1 || b2 = F -> b1 = F
or_forall {b1=F} p = Refl
or_forall {b1=T} p = p

or_cong : {b1, b2, b3 : B} -> b1 = b2 -> b1 || b3 = b2 || b3
or_cong Refl = Refl

total
ite_same : {a : Type} -> (b : B) -> (x : a) -> (ite b x x) = x
ite_same T x = Refl
ite_same F x = Refl


b_contra : F = T -> {P : Type} -> P
b_contra Refl impossible
