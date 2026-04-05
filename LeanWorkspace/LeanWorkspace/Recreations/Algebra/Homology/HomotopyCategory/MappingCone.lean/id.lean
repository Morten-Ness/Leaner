import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem id :
    (CochainComplex.mappingCone.fst φ).1.comp (CochainComplex.mappingCone.inl φ) (add_neg_cancel 1) +
      (CochainComplex.mappingCone.snd φ).comp (Cochain.ofHom (CochainComplex.mappingCone.inr φ)) (add_zero 0) = Cochain.ofHom (𝟙 _) := by
  simp [CochainComplex.mappingCone.ext_cochain_from_iff φ (-1) 0 (neg_add_cancel 1)]

