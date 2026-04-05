import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_self_inj [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b := (@strictMonoOn_mul_self R _).eq_iff_eq h1 h2

