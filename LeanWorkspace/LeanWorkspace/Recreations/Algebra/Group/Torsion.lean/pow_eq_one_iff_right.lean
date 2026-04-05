import Mathlib

variable {M G : Type*}

variable [Monoid M]

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

theorem pow_eq_one_iff_right (ha : a ≠ 1) : a ^ n = 1 ↔ n = 0 := by simp [*]

