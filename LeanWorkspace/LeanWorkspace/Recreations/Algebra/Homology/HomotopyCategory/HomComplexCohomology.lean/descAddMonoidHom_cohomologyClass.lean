import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

variable {G : Type*} [AddCommGroup G]
  (f : Cocycle K L n →+ G) (hf : coboundaries K L n ≤ f.ker)

theorem descAddMonoidHom_cohomologyClass (x : Cocycle K L n) :
    CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom f hf (CochainComplex.HomComplex.CohomologyClass.mk x) = f x := rfl

