import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem set_smul_le_iff (p : Submodule R M) :
    s • N ≤ p ↔
    ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p := by
  fconstructor
  · intro h r n hr hn
    exact h <| Submodule.mem_set_smul_of_mem_mem hr hn
  · apply Submodule.set_smul_le

