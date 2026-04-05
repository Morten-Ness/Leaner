import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inl_fst :
    (CochainComplex.mappingCone.inl φ).comp (CochainComplex.mappingCone.fst φ).1 (neg_add_cancel 1) = Cochain.ofHom (𝟙 F) := by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_cancel 1) p (p - 1) p rfl (by lia)]

