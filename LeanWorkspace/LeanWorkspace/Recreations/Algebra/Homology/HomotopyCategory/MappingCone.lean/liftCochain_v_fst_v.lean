import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} {n m : ℤ}

variable (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)

theorem liftCochain_v_fst_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃) :
    (CochainComplex.mappingCone.liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (CochainComplex.mappingCone.fst φ).1.v p₂ p₃ h₂₃ = α.v p₁ p₃ (by lia) := by
  simpa only [Cochain.comp_v _ _ h p₁ p₂ p₃ h₁₂ h₂₃]
    using Cochain.congr_v (CochainComplex.mappingCone.liftCochain_fst φ α β h) p₁ p₃ (by lia)

