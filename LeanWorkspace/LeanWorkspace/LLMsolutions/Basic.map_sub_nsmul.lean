FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x - n • a) = f x - n • b := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, sub_eq_add_neg, sub_eq_add_neg, ← add_assoc]
      rw [AddConstMapClass.map_add_const (F := F) (f := f) (x := x - n • a)]
      rw [ih]
      simp [succ_nsmul, sub_eq_add_neg, add_assoc]
