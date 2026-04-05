import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem comp_zero_cochain_v (z₁ : CochainComplex.HomComplex.Cochain F G n) (z₂ : CochainComplex.HomComplex.Cochain G K 0) (p q : ℤ) (hpq : p + n = q) :
    (z₁.comp z₂ (add_zero n)).v p q hpq = z₁.v p q hpq ≫ z₂.v q q (add_zero q) := CochainComplex.HomComplex.Cochain.comp_v z₁ z₂ (add_zero n) p q q hpq (add_zero q)

