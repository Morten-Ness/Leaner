import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain M K n) (β : Cochain M L m) (h : m + 1 = n)

set_option backward.isDefEq.respectTransparency false in
theorem liftCochain_v_fst_f (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (CochainComplex.mappingCocone.liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (CochainComplex.mappingCocone.fst φ).f p₂ = α.v p₁ p₂ h₁₂ := by
  simp [CochainComplex.mappingCocone.liftCochain, CochainComplex.mappingCocone, CochainComplex.mappingCocone.fst,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p₂ _ (p₂ + -1) (by lia)]

