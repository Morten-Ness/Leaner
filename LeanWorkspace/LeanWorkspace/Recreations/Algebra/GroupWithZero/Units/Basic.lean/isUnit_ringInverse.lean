import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem isUnit_ringInverse {a : M₀} : IsUnit a⁻¹ʳ ↔ IsUnit a := ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero,
    IsUnit.ringInverse⟩

