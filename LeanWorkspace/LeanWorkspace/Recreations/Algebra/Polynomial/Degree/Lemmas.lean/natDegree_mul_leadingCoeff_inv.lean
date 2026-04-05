import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable {K : Type*} [DivisionRing K]

theorem natDegree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q ≠ 0) :
    natDegree (p * Polynomial.C (leadingCoeff q)⁻¹) = natDegree p := natDegree_eq_of_degree_eq (Polynomial.degree_mul_leadingCoeff_inv _ h)

