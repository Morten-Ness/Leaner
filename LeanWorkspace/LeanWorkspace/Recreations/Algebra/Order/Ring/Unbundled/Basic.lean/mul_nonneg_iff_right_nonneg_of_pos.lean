import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_nonneg_iff_right_nonneg_of_pos [PosMulStrictMono R]
    (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b := ⟨fun h => nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩

