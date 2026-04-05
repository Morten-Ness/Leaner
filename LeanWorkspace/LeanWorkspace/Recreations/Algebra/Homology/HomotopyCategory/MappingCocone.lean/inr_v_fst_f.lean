import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem inr_v_fst_f (p q : ℤ) (hpq : p + 1 = q) :
    (CochainComplex.mappingCocone.inr φ).1.v p q hpq ≫ (CochainComplex.mappingCocone.fst φ).f q = 0 := by
  simp [CochainComplex.mappingCocone.inr, CochainComplex.mappingCocone.fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

