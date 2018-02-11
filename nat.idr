
data N : Type where
  Z : N
  S : N -> N

(+) : N -> N -> N
(+) Z y = y
(+) (S x) y = S (x + y)



zplus : {x : N} -> Z + x = x
zplus = Refl

total
zplus_a : {x : N} -> x + Z = x
zplus_a {x=Z} = Refl
zplus_a {x=(S x)} = rewrite zplus_a{x=x} in Refl

plus_comm_s : (x : N) -> (y : N) -> S (y + x) = y + S x
plus_comm_s x Z = Refl
plus_comm_s x (S y) = rewrite plus_comm_s x y in Refl


plus_comm : (x, y : N) -> x + y = y + x
plus_comm Z y = sym (zplus_a {x = y})
plus_comm (S x) y = rewrite plus_comm x y in (plus_comm_s x y)

plus_assoc : (x, y, z : N) -> x + (y + z) = (x + y) + z
plus_assoc Z y z = Refl
plus_assoc (S x) y z = rewrite plus_assoc x y z in Refl

plus_assoc1 : (x, y, z : N) -> x + (y + z) = y + (x + z)
plus_assoc1 x y z = trans (plus_assoc x y z) (rewrite (plus_comm x y) in sym (plus_assoc y x z))



(*) : N -> N -> N
(*) Z y = Z
(*) (S x) y = y + (x * y)

mul_rdistr : (x, y, z : N) -> (x + y)*z = x*z + y*z
mul_rdistr Z y z = Refl
mul_rdistr (S x) y z = rewrite mul_rdistr x y z in plus_assoc z (x * z) (y * z)

mul_comm_rhs_5 : (y : N) -> Z = (y * Z)
mul_comm_rhs_5 Z = Refl
mul_comm_rhs_5 (S x) = mul_comm_rhs_5 x

mul_succ : (x, y : N) -> x * (S y) = x + x * y
mul_succ Z y = Refl
mul_succ (S x) y = rewrite mul_succ x y in (rewrite plus_assoc1 y x (x * y) in  Refl)

mul_comm_succ_z : (y : N) -> (y + Z) = (y * (S Z))
mul_comm_succ_z Z = Refl
mul_comm_succ_z (S x) = rewrite mul_comm_succ_z x in Refl

mul_comm_succ : (x : N) -> (y : N) -> (y + (x * y)) = (y * (S x))
mul_comm_succ Z y = mul_comm_succ_z y
-- mul_comm_succ Z y = trans (zplus_a {x=y}) (sym (trans (mul_succ y Z) (rewrite sym (mul_comm_rhs_5 y) in zplus_a {x=y})))
mul_comm_succ (S x) y = rewrite mul_comm_succ x y in sym (mul_succ y (S x))

total
mul_comm : (x, y : N) -> x*y = y*x
mul_comm Z y = mul_comm_rhs_5 y
mul_comm (S x) y = mul_comm_succ x y

total
mul_assoc : (x, y, z : N) -> x * (y * z) = (x * y) * z
mul_assoc Z y z = Refl
mul_assoc (S x) y z = rewrite mul_assoc x y z in sym (mul_rdistr y (x * y) z)
