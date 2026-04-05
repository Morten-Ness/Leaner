import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem pi_eq_bot_iff (S : ∀ i, Submonoid (M i)) : Submonoid.pi Set.univ S = ⊥ ↔ ∀ i, S i = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

