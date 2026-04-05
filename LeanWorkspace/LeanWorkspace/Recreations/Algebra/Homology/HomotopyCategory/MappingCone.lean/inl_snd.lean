import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inl_snd :
    (CochainComplex.mappingCone.inl φ).comp (CochainComplex.mappingCone.snd φ) (add_zero (-1)) = 0 := by
  ext
  simp

