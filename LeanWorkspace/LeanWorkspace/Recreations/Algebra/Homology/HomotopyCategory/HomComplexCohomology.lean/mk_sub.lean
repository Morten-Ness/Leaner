import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

theorem mk_sub (x y : Cocycle K L n) :
    CochainComplex.HomComplex.CohomologyClass.mk (x - y) = CochainComplex.HomComplex.CohomologyClass.mk x - CochainComplex.HomComplex.CohomologyClass.mk y := rfl

