import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem set_smul_eq_iSup [SMulCommClass S R M] (s : Set S) (N : Submodule R M) :
    s • N = ⨆ (a ∈ s), a • N := by
  refine Eq.trans (congrArg sInf ?_) csInf_Ici
  simp_rw [← Set.Ici_def, iSup_le_iff, @forall_comm M]
  exact Set.ext fun _ => forall₂_congr (fun _ _ => Iff.symm map_le_iff_le_comap)

