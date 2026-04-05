import Mathlib

variable {G : Type*}

variable {α : Type*} (P : Prop) [Decidable P]

variable [Mul α]

theorem mul_dite (a : α) (b : P → α) (c : ¬P → α) :
    (a * if h : P then b h else c h) = if h : P then a * b h else a * c h := by split <;> rfl

