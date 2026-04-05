import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem IsKInjective.rightOrthogonal (L : CochainComplex C ℤ) [L.IsKInjective] :
    (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  rwa [← CochainComplex.isKInjective_iff_rightOrthogonal]

