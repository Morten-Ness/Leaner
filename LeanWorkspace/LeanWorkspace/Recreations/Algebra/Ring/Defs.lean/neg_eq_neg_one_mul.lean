import Mathlib

variable {α : Type u} {R : Type v}

variable [MulOneClass α] [HasDistribNeg α]

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by simp

