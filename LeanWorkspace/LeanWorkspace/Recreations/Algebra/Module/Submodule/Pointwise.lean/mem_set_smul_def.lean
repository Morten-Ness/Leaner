import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem mem_set_smul_def (x : M) :
    x ∈ s • N ↔
    x ∈ sInf { p : Submodule R M | ∀ ⦃r : S⦄ {n : M}, r ∈ s → n ∈ N → r • n ∈ p } := Iff.rfl

