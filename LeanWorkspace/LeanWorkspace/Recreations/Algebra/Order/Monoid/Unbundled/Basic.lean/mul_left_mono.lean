import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a) := fun _ _ h ↦ mul_le_mul_left h _

