import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem δ_inl :
    δ (-1) 0 (CochainComplex.mappingCone.inl φ) = Cochain.ofHom (φ ≫ CochainComplex.mappingCone.inr φ) := by
  ext p
  simp [δ_v (-1) 0 (neg_add_cancel 1) (CochainComplex.mappingCone.inl φ) p p (add_zero p) _ _ rfl rfl,
    CochainComplex.mappingCone.inl_v_d φ p (p - 1) (p + 1) (by lia) (by lia)]

