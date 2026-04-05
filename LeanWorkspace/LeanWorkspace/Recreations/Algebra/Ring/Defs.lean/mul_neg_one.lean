import Mathlib

variable {α : Type u} {R : Type v}

variable [MulOneClass α] [HasDistribNeg α]

theorem mul_neg_one (a : α) : a * -1 = -a := by simp

