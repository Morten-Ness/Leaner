import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
theorem inr_v_snd_v (p q : ℤ) (hpq : p + 1 = q) :
    (CochainComplex.mappingCocone.inr φ).1.v p q hpq ≫ (CochainComplex.mappingCocone.snd φ).v q p (by lia) = 𝟙 _ := by
  simp [CochainComplex.mappingCocone.inr, CochainComplex.mappingCocone.snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

