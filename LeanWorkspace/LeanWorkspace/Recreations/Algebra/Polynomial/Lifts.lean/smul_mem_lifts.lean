import Mathlib

open scoped Polynomial

variable {R : Type u} [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]

theorem smul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ Polynomial.lifts (algebraMap R S)) :
    r • p ∈ Polynomial.lifts (algebraMap R S) := by
  rw [Polynomial.mem_lifts_iff_mem_alg] at hp ⊢
  exact Subalgebra.smul_mem (mapAlg R S).range hp r

