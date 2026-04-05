import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem inl_v_fst_v (p q : ℤ) (hpq : q + 1 = p) :
    (CochainComplex.mappingCone.inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫
      (CochainComplex.mappingCone.fst φ : Cochain (CochainComplex.mappingCone φ) F 1).v q p hpq = 𝟙 _ := by
  simp [CochainComplex.mappingCone.inl, CochainComplex.mappingCone.fst]

