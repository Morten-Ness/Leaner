import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inr_fst :
    (Cochain.ofHom (CochainComplex.mappingCone.inr φ)).comp (CochainComplex.mappingCone.fst φ).1 (zero_add 1) = 0 := by
  ext
  simp

