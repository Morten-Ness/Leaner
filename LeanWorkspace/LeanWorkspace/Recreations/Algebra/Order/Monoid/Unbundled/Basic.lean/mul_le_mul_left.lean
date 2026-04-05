import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LE α]

theorem mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b ≤ c) (a : α) : b * a ≤ c * a := i.elim a bc

