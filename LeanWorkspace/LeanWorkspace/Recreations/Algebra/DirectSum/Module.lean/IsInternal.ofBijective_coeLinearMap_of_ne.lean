import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem IsInternal.ofBijective_coeLinearMap_of_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) (x : A i) :
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm x j = 0 := by
  rw [← DirectSum.coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_of_ne i j _ hij.symm]

