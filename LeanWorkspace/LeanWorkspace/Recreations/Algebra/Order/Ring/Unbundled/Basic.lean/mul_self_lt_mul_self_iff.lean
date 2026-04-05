import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_self_lt_mul_self_iff [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b := ((@strictMonoOn_mul_self R _).lt_iff_lt h1 h2).symm

