import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_ofNat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) • b := AddConstMapClass.map_nat_add' f n x

