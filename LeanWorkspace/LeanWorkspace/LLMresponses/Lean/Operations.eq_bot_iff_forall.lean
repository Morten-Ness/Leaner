import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem eq_bot_iff_forall : S = ⊥ ↔ ∀ x ∈ S, x = (1 : M) := by
  constructor
  · intro h
    intro x hx
    rw [h] at hx
    exact hx
  · intro h
    ext x
    constructor
    · intro hx
      rw [h x hx]
      exact show (1 : M) ∈ (⊥ : Submonoid M) by rw [Submonoid.mem_bot]
    · intro hx
      rw [Submonoid.mem_bot] at hx
      rw [hx]
      exact S.one_mem
