import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LE α]

theorem mul_le_mul_iff_right [MulRightMono α]
    [MulRightReflectLE α] (a : α) {b c : α} :
    b * a ≤ c * a ↔ b ≤ c := rel_iff_cov α α (swap (· * ·)) (· ≤ ·) a

