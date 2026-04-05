import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem prod_le_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    s.prod t ≤ u ↔ s.map (inl M N) ≤ u ∧ t.map (inr M N) ≤ u := by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, Submonoid.one_mem _⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨Submonoid.one_mem _, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : inl M N x1 ∈ u := by
      apply hH
      simpa using h1
    have h2' : inr M N x2 ∈ u := by
      apply hK
      simpa using h2
    simpa using Submonoid.mul_mem _ h1' h2'

