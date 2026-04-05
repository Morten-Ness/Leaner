import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem erase_mem_lifts {p : S[X]} (n : ℕ) (h : p ∈ Polynomial.lifts f) : p.erase n ∈ Polynomial.lifts f := by
  rw [Polynomial.lifts_iff_ringHom_rangeS, mem_map_rangeS] at h ⊢
  intro k
  by_cases hk : k = n
  · use 0
    simp only [hk, map_zero, erase_same]
  obtain ⟨i, hi⟩ := h k
  use i
  simp only [hi, hk, erase_ne, Ne, not_false_iff]

