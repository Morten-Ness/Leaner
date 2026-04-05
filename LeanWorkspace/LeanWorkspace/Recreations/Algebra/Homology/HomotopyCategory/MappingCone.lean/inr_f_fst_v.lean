import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem inr_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (CochainComplex.mappingCone.inr φ).f p ≫ (CochainComplex.mappingCone.fst φ).1.v p q hpq = 0 := by
  simp [CochainComplex.mappingCone.inr, CochainComplex.mappingCone.fst]

