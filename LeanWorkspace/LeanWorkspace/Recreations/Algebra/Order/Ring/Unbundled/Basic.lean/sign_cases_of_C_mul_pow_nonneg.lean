import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem sign_cases_of_C_mul_pow_nonneg [PosMulStrictMono R]
    (h : ∀ n, 0 ≤ a * b ^ n) : a = 0 ∨ 0 < a ∧ 0 ≤ b := by
  have : 0 ≤ a := by simpa only [pow_zero, mul_one] using h 0
  refine this.eq_or_lt'.imp_right fun ha ↦ ⟨ha, nonneg_of_mul_nonneg_right ?_ ha⟩
  simpa only [pow_one] using h 1

