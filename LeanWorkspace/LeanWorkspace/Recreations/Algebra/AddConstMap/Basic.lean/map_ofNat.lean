import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] :
    f ofNat(n) = f 0 + ofNat(n) := AddConstMapClass.map_nat f n

