import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LE α]

theorem mul_le_mul_iff_left [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b c : α} :
    a * b ≤ a * c ↔ b ≤ c := rel_iff_cov α α (· * ·) (· ≤ ·) a

