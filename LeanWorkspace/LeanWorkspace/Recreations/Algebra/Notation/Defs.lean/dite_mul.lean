import Mathlib

variable {G : Type*}

variable {α : Type*} (P : Prop) [Decidable P]

variable [Mul α]

theorem dite_mul (a : P → α) (b : ¬P → α) (c : α) :
    (if h : P then a h else b h) * c = if h : P then a h * c else b h * c := by split <;> rfl

