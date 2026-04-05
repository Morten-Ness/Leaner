import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_nonneg_iff_left_nonneg_of_pos [PosMulStrictMono R] [MulPosStrictMono R]
    (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a := ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => mul_nonneg h hb.le⟩

