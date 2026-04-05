import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} {n m : ℤ}

variable (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n)

theorem inl_v_descCochain_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃) :
    (CochainComplex.mappingCone.inl φ).v p₁ p₂ h₁₂ ≫ (CochainComplex.mappingCone.descCochain φ α β h).v p₂ p₃ h₂₃ =
        α.v p₁ p₃ (by rw [← h₂₃, ← h₁₂, ← h, add_comm m, add_assoc, neg_add_cancel_left]) := by
  simpa only [Cochain.comp_v _ _ (show -1 + n = m by lia) p₁ p₂ p₃
    (by lia) (by lia)] using
      Cochain.congr_v (CochainComplex.mappingCone.inl_descCochain φ α β h) p₁ p₃ (by lia)

