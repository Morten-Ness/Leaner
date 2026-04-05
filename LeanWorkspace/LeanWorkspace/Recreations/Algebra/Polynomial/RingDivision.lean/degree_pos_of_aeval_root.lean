import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] {p q : R[X]}

variable [Semiring S]

theorem degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S} (hz : Polynomial.aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (Polynomial.natDegree_pos_of_aeval_root hp hz inj)

