import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C]

theorem isIso₂_of_shortExact_of_isIso₁₃ [Balanced C] {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [IsIso φ.τ₁] [IsIso φ.τ₃] : IsIso φ.τ₂ := by
  have := h₁.mono_f
  have := h₂.mono_f
  have := h₁.epi_g
  have := h₂.epi_g
  have := mono_τ₂_of_exact_of_mono φ h₁.exact
  have := epi_τ₂_of_exact_of_epi φ h₂.exact
  apply isIso_of_mono_of_epi

