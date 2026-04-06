FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) : f n = f 0 + n • b := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.succ_eq_add_one, map_add]
      simp [ih, add_assoc, add_left_comm, add_comm]
