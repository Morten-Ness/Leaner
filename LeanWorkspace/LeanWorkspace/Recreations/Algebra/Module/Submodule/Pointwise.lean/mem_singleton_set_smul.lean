import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem mem_singleton_set_smul [SMulCommClass R S M] (r : S) (x : M) :
    x ∈ ({r} : Set S) • N ↔ ∃ (m : M), m ∈ N ∧ x = r • m := by
  fconstructor
  · intro hx
    induction x, hx using Submodule.set_smul_inductionOn with
    | smul₀ => aesop
    | @smul₁ t n mem h =>
      rcases h with ⟨n, hn, rfl⟩
      exact ⟨t • n, by aesop, smul_comm _ _ _⟩
    | add mem₁ mem₂ h₁ h₂ =>
      rcases h₁ with ⟨m₁, h₁, rfl⟩
      rcases h₂ with ⟨m₂, h₂, rfl⟩
      exact ⟨m₁ + m₂, Submodule.add_mem _ h₁ h₂, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  · aesop

