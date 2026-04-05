import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_ofNat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) := AddConstMapClass.map_nat_add f n x

