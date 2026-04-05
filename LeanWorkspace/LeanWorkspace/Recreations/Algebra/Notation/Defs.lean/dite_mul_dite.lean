import Mathlib

variable {G : Type*}

variable {α : Type*} (P : Prop) [Decidable P]

variable [Mul α]

theorem dite_mul_dite (a : P → α) (b : ¬P → α) (c : P → α) (d : ¬P → α) :
    ((if h : P then a h else b h) * if h : P then c h else d h) =
      if h : P then a h * c h else b h * d h := by split <;> rfl

