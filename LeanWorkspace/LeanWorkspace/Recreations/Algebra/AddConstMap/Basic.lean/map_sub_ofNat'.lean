import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x - ofNat(n)) = f x - ofNat(n) • b := AddConstMapClass.map_sub_nat' f x n

