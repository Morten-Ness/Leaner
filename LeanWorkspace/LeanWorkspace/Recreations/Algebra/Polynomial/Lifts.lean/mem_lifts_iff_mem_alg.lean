import Mathlib

open scoped Polynomial

variable {R : Type u} [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]

theorem mem_lifts_iff_mem_alg (R : Type u) [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]
    (p : S[X]) : p ∈ Polynomial.lifts (algebraMap R S) ↔ p ∈ AlgHom.range (@mapAlg R _ S _ _) := by
  simp only [coe_mapRingHom, Polynomial.lifts, mapAlg_eq_map, AlgHom.mem_range, RingHom.mem_rangeS]

