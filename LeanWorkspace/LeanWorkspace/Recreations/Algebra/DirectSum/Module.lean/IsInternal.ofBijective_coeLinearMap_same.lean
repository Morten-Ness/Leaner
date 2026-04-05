import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem IsInternal.ofBijective_coeLinearMap_same (h : IsInternal A)
    {i : ι} (x : A i) :
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm x i = x := by
  rw [← DirectSum.coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_same]

