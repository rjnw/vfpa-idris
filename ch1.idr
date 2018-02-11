

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

nelim : (b : B) -> not (not b) = b
nelim T = Refl
nelim F = Refl

same_and : {b : B} -> b && b = b
same_and {b = T} = Refl
same_and {b = F} = Refl
