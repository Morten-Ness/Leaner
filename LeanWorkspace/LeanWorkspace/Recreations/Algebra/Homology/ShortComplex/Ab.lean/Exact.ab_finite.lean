import Mathlib

variable (S : ShortComplex Ab.{u})

theorem Exact.ab_finite {S : CategoryTheory.ShortComplex Ab.{u}} (hS : S.Exact) [Finite S.X₁] [Finite S.X₃] :
    Finite S.X₂ := by
  have : Finite S.f.hom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.range) := by
    rw [hS.ab_range_eq_ker]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  exact .of_addSubgroup_quotient (H := S.f.hom.range)

