import Mathlib

variable {M N : Type*}

theorem finTwoArrowEquiv'_sum_eq {d : M × M} [AddCommMonoid M] :
    (((finTwoArrowEquiv' M).symm d).sum fun _ n ↦ n) = d.1 + d.2 := by
  apply (Finsupp.equivFunOnFinite_symm_sum _).trans
  simp

