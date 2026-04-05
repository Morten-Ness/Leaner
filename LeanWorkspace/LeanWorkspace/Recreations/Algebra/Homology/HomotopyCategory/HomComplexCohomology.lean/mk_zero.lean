import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

theorem mk_zero :
    CochainComplex.HomComplex.CohomologyClass.mk (0 : Cocycle K L n) = 0 := rfl

