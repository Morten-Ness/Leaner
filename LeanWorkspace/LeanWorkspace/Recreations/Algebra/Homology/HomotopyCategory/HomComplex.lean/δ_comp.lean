import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁) (h₂ : n₂ + 1 = m₂) :
    CochainComplex.HomComplex.δ n₁₂ m₁₂ (z₁.comp z₂ h) = z₁.comp (CochainComplex.HomComplex.δ n₂ m₂ z₂) (by rw [← h₁₂, ← h₂, ← h, add_assoc]) +
      n₂.negOnePow • (CochainComplex.HomComplex.δ n₁ m₁ z₁).comp z₂
        (by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]) := by
  subst h₁₂ h₁ h₂ h
  ext p q hpq
  dsimp
  rw [CochainComplex.HomComplex.Cochain.comp_v z₁ _ (add_assoc n₁ n₂ 1).symm p _ q rfl (by lia),
    CochainComplex.HomComplex.Cochain.comp_v _ _ (show n₁ + 1 + n₂ = n₁ + n₂ + 1 by lia) p (p + n₁ + 1) q
      (by lia) (by lia),
    CochainComplex.HomComplex.δ_v (n₁ + n₂) _ rfl (z₁.comp z₂ rfl) p q hpq (p + n₁ + n₂) _ (by lia) rfl,
    CochainComplex.HomComplex.Cochain.comp_v z₁ z₂ rfl p _ _ rfl rfl,
    CochainComplex.HomComplex.Cochain.comp_v z₁ z₂ rfl (p + 1) (p + n₁ + 1) q (by lia) (by lia),
    CochainComplex.HomComplex.δ_v n₂ (n₂ + 1) rfl z₂ (p + n₁) q (by lia) (p + n₁ + n₂) _ (by lia) rfl,
    CochainComplex.HomComplex.δ_v n₁ (n₁ + 1) rfl z₁ p (p + n₁ + 1) (by lia) (p + n₁) _ (by lia) rfl]
  simp only [assoc, comp_add, add_comp, Int.negOnePow_succ, Int.negOnePow_add n₁ n₂,
    Units.neg_smul, comp_neg, neg_comp, smul_neg, smul_smul, Linear.units_smul_comp,
    mul_comm n₁.negOnePow n₂.negOnePow, Linear.comp_units_smul, smul_add]
  abel

