import Mathlib

variable {α : Type u} {R : Type v}

variable [MulOneClass α] [HasDistribNeg α]

theorem neg_one_mul (a : α) : -1 * a = -a := by simp

