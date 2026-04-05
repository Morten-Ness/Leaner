import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem singleton_set_smul [SMulCommClass S R M] (r : S) : ({r} : Set S) • N = r • N := by
  apply Submodule.set_smul_eq_of_le
  · rintro _ m rfl hm; exact ⟨m, hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [Submodule.mem_set_smul_def, Submodule.mem_sInf]
    intro _ hp; exact hp rfl hm

