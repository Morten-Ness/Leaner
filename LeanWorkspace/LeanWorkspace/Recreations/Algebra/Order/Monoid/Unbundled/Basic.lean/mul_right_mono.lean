import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·) := fun _ _ h ↦ mul_le_mul_right h _

