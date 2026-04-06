FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_nsmul [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x + n • a) = f x + n • b := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, ← add_assoc, AddConstMapClass.map_add_const, ih, succ_nsmul]
