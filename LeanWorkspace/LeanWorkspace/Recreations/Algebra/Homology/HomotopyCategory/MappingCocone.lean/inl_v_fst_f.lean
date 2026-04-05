import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem inl_v_fst_f (p : ℤ) :
    (CochainComplex.mappingCocone.inl φ).v p p (add_zero p) ≫ (CochainComplex.mappingCocone.fst φ).f p = 𝟙 _ := by
  simp [CochainComplex.mappingCocone.inl, CochainComplex.mappingCocone.fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

