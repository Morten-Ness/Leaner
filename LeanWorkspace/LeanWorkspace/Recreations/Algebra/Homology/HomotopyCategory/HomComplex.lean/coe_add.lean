import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem coe_add (z₁ z₂ : CochainComplex.HomComplex.Cocycle F G n) :
    (↑(z₁ + z₂) : CochainComplex.HomComplex.Cochain F G n) = (z₁ : CochainComplex.HomComplex.Cochain F G n) + (z₂ : CochainComplex.HomComplex.Cochain F G n) := rfl

