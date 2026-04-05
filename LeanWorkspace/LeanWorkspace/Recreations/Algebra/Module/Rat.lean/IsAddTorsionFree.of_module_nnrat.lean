import Mathlib

variable {M M₂ : Type*}

theorem IsAddTorsionFree.of_module_nnrat [AddCommMonoid M] [Module ℚ≥0 M] : IsAddTorsionFree M where
  nsmul_right_injective n hn x y hxy := by
    simpa [← Nat.cast_smul_eq_nsmul ℚ≥0 n, *] using congr((n⁻¹ : ℚ≥0) • $hxy)

