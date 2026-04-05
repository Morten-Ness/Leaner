import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + (ofNat(n) : ℕ) • b := AddConstMapClass.map_add_nat' f x n

