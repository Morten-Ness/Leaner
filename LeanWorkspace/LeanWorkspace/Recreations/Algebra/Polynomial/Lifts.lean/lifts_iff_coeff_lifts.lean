import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem lifts_iff_coeff_lifts (p : S[X]) : p ∈ Polynomial.lifts f ↔ ∀ n : ℕ, p.coeff n ∈ Set.range f := by
  rw [Polynomial.lifts_iff_ringHom_rangeS, mem_map_rangeS f]
  rfl

