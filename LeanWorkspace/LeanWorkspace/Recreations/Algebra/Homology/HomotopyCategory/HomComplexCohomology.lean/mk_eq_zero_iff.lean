import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

theorem mk_eq_zero_iff (x : Cocycle K L n) :
    CochainComplex.HomComplex.CohomologyClass.mk x = 0 ↔ x ∈ CochainComplex.HomComplex.coboundaries K L n := QuotientAddGroup.eq_zero_iff x

