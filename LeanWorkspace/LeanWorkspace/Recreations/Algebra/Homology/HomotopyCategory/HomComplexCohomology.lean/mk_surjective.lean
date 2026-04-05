import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

theorem mk_surjective : Function.Surjective (CochainComplex.HomComplex.CohomologyClass.mk : Cocycle K L n → _) := Quotient.mk_surjective

