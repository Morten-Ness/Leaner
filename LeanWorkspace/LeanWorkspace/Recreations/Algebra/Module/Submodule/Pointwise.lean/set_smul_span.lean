import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem set_smul_span [SMulCommClass S R M] (s : Set S) (t : Set M) :
    s • span R t = span R (s • t) := by
  simp_rw [Submodule.set_smul_eq_iSup, Submodule.smul_span, iSup_span, Set.iUnion_smul_set]

