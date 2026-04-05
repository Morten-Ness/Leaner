import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem inr_f_snd_v (p : ℤ) :
    (CochainComplex.mappingCone.inr φ).f p ≫ (CochainComplex.mappingCone.snd φ).v p p (add_zero p) = 𝟙 _ := by
  simp [CochainComplex.mappingCone.inr, CochainComplex.mappingCone.snd]

