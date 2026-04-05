import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem mem_set_smul_of_mem_mem {r : S} {m : M} (mem1 : r ∈ s) (mem2 : m ∈ N) :
    r • m ∈ s • N := by
  rw [Submodule.mem_set_smul_def, mem_sInf]
  exact fun _ h => h mem1 mem2

