import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem id_X (p q : ℤ) (hpq : p + -1 = q) :
    (CochainComplex.mappingCocone.fst φ).f p ≫ (CochainComplex.mappingCocone.inl φ).v p p (add_zero p) +
      (CochainComplex.mappingCocone.snd φ).v p q hpq ≫ (CochainComplex.mappingCocone.inr φ).1.v q p (by lia) = 𝟙 _ := by
  obtain rfl : q = p + -1 := by lia
  simp [CochainComplex.mappingCocone.fst, CochainComplex.mappingCocone.inl, CochainComplex.mappingCocone.snd, CochainComplex.mappingCocone.inr, CochainComplex.mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Int.negOnePow_even 2 ⟨1, rfl⟩,
    mappingCone.id_X φ (p + -1) p (by lia)]

