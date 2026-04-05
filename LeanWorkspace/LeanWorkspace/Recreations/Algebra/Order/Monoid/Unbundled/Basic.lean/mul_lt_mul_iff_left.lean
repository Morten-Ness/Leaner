import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LT α]

theorem mul_lt_mul_iff_left [MulLeftStrictMono α]
    [MulLeftReflectLT α] (a : α) {b c : α} :
    a * b < a * c ↔ b < c := rel_iff_cov α α (· * ·) (· < ·) a

