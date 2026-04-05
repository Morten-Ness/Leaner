import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

theorem noZeroDivisors_iff_right_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → ∀ y, x * y = 0 → y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h a ha b eq ↦ h eq ha, fun h a b eq ha ↦ h a ha b eq⟩

