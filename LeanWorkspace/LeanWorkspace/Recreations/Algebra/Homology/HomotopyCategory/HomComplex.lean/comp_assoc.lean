import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K n₂) (z₃ : CochainComplex.HomComplex.Cochain K L n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    (z₁.comp z₂ h₁₂).comp z₃ (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) =
      z₁.comp (z₂.comp z₃ h₂₃) (by rw [← h₂₃, ← h₁₂₃, add_assoc]) := by
  substs h₁₂ h₂₃ h₁₂₃
  ext p q hpq
  rw [CochainComplex.HomComplex.Cochain.comp_v _ _ rfl p (p + n₁ + n₂) q (add_assoc _ _ _).symm (by lia),
    CochainComplex.HomComplex.Cochain.comp_v z₁ z₂ rfl p (p + n₁) (p + n₁ + n₂) (by lia) (by lia),
    CochainComplex.HomComplex.Cochain.comp_v z₁ (z₂.comp z₃ rfl) (add_assoc n₁ n₂ n₃).symm p (p + n₁) q (by lia) (by lia),
    CochainComplex.HomComplex.Cochain.comp_v z₂ z₃ rfl (p + n₁) (p + n₁ + n₂) q (by lia) (by lia), assoc]

