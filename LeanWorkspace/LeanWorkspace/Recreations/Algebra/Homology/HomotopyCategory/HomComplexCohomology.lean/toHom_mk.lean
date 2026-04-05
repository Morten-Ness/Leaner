import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

theorem toHom_mk (x : Cocycle K L n) :
    CochainComplex.HomComplex.CohomologyClass.toHom (CochainComplex.HomComplex.CohomologyClass.mk x) = (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) := rfl

