import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem inl_v_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (CochainComplex.mappingCocone.inl φ).v p p (add_zero p) ≫ (CochainComplex.mappingCocone.snd φ).v p q hpq = 0 := by
  obtain rfl : q = p + -1 := by lia
  simp [CochainComplex.mappingCocone.inl, CochainComplex.mappingCocone.snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

