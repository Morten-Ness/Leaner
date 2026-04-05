import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_self_le_mul_self_iff [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b := ⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

