import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n • b := by simp [← AddConstMapClass.map_add_nsmul]

