import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem lifts_iff_ringHom_rangeS (p : S[X]) : p ∈ Polynomial.lifts f ↔ p ∈ (mapRingHom f).rangeS := by
  simp only [coe_mapRingHom, Polynomial.lifts, RingHom.mem_rangeS]

