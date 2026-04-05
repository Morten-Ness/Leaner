import Mathlib

open scoped Polynomial

variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R →+* S)

theorem lifts_iff_liftsRing (p : S[X]) : p ∈ Polynomial.lifts f ↔ p ∈ Polynomial.liftsRing f := by
  simp only [Polynomial.lifts, Polynomial.liftsRing, RingHom.mem_range, RingHom.mem_rangeS]

