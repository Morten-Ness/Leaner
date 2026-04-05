import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain M K n) (β : Cochain M L m) (h : m + 1 = n)

set_option backward.isDefEq.respectTransparency false in
theorem liftCochain_v_snd_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = p₃) :
    (CochainComplex.mappingCocone.liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (CochainComplex.mappingCocone.snd φ).v p₂ p₃ h₂₃ = β.v p₁ p₃ (by lia) := by
  subst h₂₃
  simp [CochainComplex.mappingCocone.liftCochain, CochainComplex.mappingCocone, CochainComplex.mappingCocone.snd,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ _ (add_zero _),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

