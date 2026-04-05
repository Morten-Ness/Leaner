import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_zero_cochain_comp {n₂ : ℤ} (z₁ : CochainComplex.HomComplex.Cochain F G 0) (z₂ : CochainComplex.HomComplex.Cochain G K n₂)
    (m₂ : ℤ) (h₂ : n₂ + 1 = m₂) :
    CochainComplex.HomComplex.δ n₂ m₂ (z₁.comp z₂ (zero_add n₂)) =
      z₁.comp (CochainComplex.HomComplex.δ n₂ m₂ z₂) (zero_add m₂) +
      n₂.negOnePow • ((CochainComplex.HomComplex.δ 0 1 z₁).comp z₂ (by rw [add_comm, h₂])) := CochainComplex.HomComplex.δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

