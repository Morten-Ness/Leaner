import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem comp_v {n₁ n₂ n₁₂ : ℤ} (z₁ : CochainComplex.HomComplex.Cochain F G n₁) (z₂ : CochainComplex.HomComplex.Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (p₁ p₂ p₃ : ℤ) (h₁ : p₁ + n₁ = p₂) (h₂ : p₂ + n₂ = p₃) :
    (z₁.comp z₂ h).v p₁ p₃ (by rw [← h₂, ← h₁, ← h, add_assoc]) =
      z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by
  subst h₁; rfl

