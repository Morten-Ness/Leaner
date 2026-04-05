import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LE α]

theorem mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b ≤ c) (a : α) : a * b ≤ a * c := CovariantClass.elim _ bc

