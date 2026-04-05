import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} {n m : ℤ}

variable (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)

theorem liftCochain_v_snd_v (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (CochainComplex.mappingCone.liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (CochainComplex.mappingCone.snd φ).v p₂ p₂ (add_zero p₂) = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (add_zero n) p₁ p₂ p₂ h₁₂ (add_zero p₂)]
    using Cochain.congr_v (CochainComplex.mappingCone.liftCochain_snd φ α β h) p₁ p₂ (by lia)

