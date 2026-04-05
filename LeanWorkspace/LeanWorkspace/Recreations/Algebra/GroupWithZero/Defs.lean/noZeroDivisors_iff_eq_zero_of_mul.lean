import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

theorem noZeroDivisors_iff_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → (∀ y, x * y = 0 → y = 0) ∧ (∀ y, y * x = 0 → y = 0) := by
  simp only [forall_and, ← noZeroDivisors_iff_right_eq_zero_of_mul,
    ← noZeroDivisors_iff_left_eq_zero_of_mul, and_self]

