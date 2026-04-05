import Mathlib

variable {M M₂ : Type*}

theorem IsAddTorsionFree.of_module_rat [AddCommGroup M] [Module ℚ M] : IsAddTorsionFree M where
  nsmul_right_injective n hn x y hxy := by
    simpa [← Nat.cast_smul_eq_nsmul ℚ n, *] using congr((n⁻¹ : ℚ) • $hxy)

