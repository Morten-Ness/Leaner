import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem zero_cochain_comp_v (z₁ : CochainComplex.HomComplex.Cochain F G 0) (z₂ : CochainComplex.HomComplex.Cochain G K n) (p q : ℤ) (hpq : p + n = q) :
    (z₁.comp z₂ (zero_add n)).v p q hpq = z₁.v p p (add_zero p) ≫ z₂.v p q hpq := CochainComplex.HomComplex.Cochain.comp_v z₁ z₂ (zero_add n) p p q (add_zero p) hpq

