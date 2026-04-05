import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem coe_neg (z : CochainComplex.HomComplex.Cocycle F G n) :
    (↑(-z) : CochainComplex.HomComplex.Cochain F G n) = -(z : CochainComplex.HomComplex.Cochain F G n) := rfl

