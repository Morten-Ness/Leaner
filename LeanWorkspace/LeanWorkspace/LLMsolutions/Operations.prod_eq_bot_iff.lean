FAIL
import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  constructor
  · intro h
    constructor
    · apply le_bot_iff.mp
      intro x hx
      have hpair : (x, (1 : N)) ∈ s.prod t := ⟨hx, t.one_mem⟩
      have : (x, (1 : N)) ∈ (⊥ : Submonoid (M × N)) := by simpa [h] using hpair
      simpa using this
    · apply le_bot_iff.mp
      intro y hy
      have hpair : ((1 : M), y) ∈ s.prod t := ⟨s.one_mem, hy⟩
      have : ((1 : M), y) ∈ (⊥ : Submonoid (M × N)) := by simpa [h] using hpair
      simpa using this
  · rintro ⟨hs, ht⟩
    ext x
    rcases x with ⟨m, n⟩
    constructor
    · intro hx
      rcases hx with ⟨hm, hn⟩
      rw [hs] at hm
      rw [ht] at hn
      simp at hm hn
      simp [hm, hn]
    · intro hx
      simp [hs, ht]
