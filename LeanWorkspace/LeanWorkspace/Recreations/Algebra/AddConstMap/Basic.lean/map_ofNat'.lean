import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] :
    f (ofNat(n)) = f 0 + (ofNat(n) : ℕ) • b := AddConstMapClass.map_nat' f n

