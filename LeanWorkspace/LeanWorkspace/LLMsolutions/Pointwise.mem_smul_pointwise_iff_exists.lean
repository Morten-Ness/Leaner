import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem mem_smul_pointwise_iff_exists (a : A) (m : M) (S : AddSubmonoid A) :
    a ∈ m • S ↔ ∃ s : A, s ∈ S ∧ m • s = a := by
  constructor
  · intro ha
    rcases ha with ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
