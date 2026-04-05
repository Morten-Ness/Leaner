import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x - n) = f x - n • b := by
  simpa using AddConstMapClass.map_sub_nsmul f x n

