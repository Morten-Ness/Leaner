import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem lifts_iff_coeffs_subset_range (p : S[X]) :
    p ∈ Polynomial.lifts f ↔ (p.coeffs : Set S) ⊆ Set.range f := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h _ hc
    obtain ⟨n, ⟨-, hn⟩⟩ := mem_coeffs_iff.mp hc
    exact hn ▸ h n
  · intro h n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact h <| coeff_mem_coeffs hn

