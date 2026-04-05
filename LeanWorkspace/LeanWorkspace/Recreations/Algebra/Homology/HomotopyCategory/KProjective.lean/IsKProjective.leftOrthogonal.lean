import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem IsKProjective.leftOrthogonal (K : CochainComplex C ℤ) [K.IsKProjective] :
    (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  rwa [← CochainComplex.isKProjective_iff_leftOrthogonal]

