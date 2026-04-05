import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem lifts_iff_set_range (p : S[X]) : p ∈ Polynomial.lifts f ↔ p ∈ Set.range (map f) := by
  simp only [coe_mapRingHom, Polynomial.lifts, Set.mem_range, RingHom.mem_rangeS]

