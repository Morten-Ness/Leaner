import Mathlib

variable {G : Type*}

variable {α : Type*} (P : Prop) [Decidable P]

variable [Mul α]

theorem ite_mul_ite (a b c d : α) :
    ((if P then a else b) * if P then c else d) = if P then a * c else b * d := by split <;> rfl

