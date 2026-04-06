FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nsmul_const [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) : f (n • a) = f 0 + n • b := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, map_add_const, ih]
      simp [add_assoc]
