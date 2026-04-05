import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n • b := by
  simpa using AddConstMapClass.map_nsmul_add f n x

