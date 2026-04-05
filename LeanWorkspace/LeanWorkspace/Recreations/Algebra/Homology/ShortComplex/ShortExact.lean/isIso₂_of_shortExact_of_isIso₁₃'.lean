import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C]

theorem isIso₂_of_shortExact_of_isIso₁₃' [Balanced C] {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (_ : IsIso φ.τ₁) (_ : IsIso φ.τ₃) : IsIso φ.τ₂ := CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂

