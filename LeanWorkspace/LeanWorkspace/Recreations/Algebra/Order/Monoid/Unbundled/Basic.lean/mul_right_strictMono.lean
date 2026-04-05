import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_right_strictMono [MulLeftStrictMono α] {a : α} : StrictMono (a * ·) := fun _ _ h ↦ mul_lt_mul_right h _

