import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} {n m : ℤ}

variable (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n)

theorem inr_f_descCochain_v (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (CochainComplex.mappingCone.inr φ).f p₁ ≫ (CochainComplex.mappingCone.descCochain φ α β h).v p₁ p₂ h₁₂ = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (zero_add n) p₁ p₁ p₂ (add_zero p₁) h₁₂, Cochain.ofHom_v]
    using Cochain.congr_v (CochainComplex.mappingCone.inr_descCochain φ α β h) p₁ p₂ (by lia)

