import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_le_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b c : R} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a := (strictAnti_mul_left h).le_iff_ge

