import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem inl_v_snd_v (p q : ℤ) (hpq : p + (-1) = q) :
    (CochainComplex.mappingCone.inl φ).v p q hpq ≫ (CochainComplex.mappingCone.snd φ).v q q (add_zero q) = 0 := by
  simp [CochainComplex.mappingCone.inl, CochainComplex.mappingCone.snd]

