import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain M K n) (β : Cochain M L m) (h : m + 1 = n)

theorem liftCochain_comp_snd :
    (CochainComplex.mappingCocone.liftCochain φ α β h).comp (CochainComplex.mappingCocone.snd φ) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₁ := n) (n₂ := -1) (n₁₂ := m) _ _ _ p _ _ (by lia)
    (Int.add_neg_cancel_right q 1)]

