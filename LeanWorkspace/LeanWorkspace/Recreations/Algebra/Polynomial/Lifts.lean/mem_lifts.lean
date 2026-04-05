import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem mem_lifts (p : S[X]) : p ∈ Polynomial.lifts f ↔ ∃ q : R[X], map f q = p := by
  simp only [coe_mapRingHom, Polynomial.lifts, RingHom.mem_rangeS]

