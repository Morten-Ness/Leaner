import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

theorem noZeroDivisors_iff_left_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → ∀ y, y * x = 0 → y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_right]
  exact ⟨fun h b hb a eq ↦ h eq hb, fun h a b eq hb ↦ h b hb a eq⟩

