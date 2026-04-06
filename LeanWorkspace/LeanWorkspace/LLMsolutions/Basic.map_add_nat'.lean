FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n • b := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      change f ((x + n) + 1) = f x + (n + 1) • b
      rw [map_add, ih, succ_nsmul, add_assoc]
