import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable {K : Type*} [DivisionRing K]

theorem natDegree_mul_leadingCoeff_self_inv (p : K[X]) :
    natDegree (p * Polynomial.C (leadingCoeff p)⁻¹) = natDegree p := natDegree_eq_of_degree_eq (Polynomial.degree_mul_leadingCoeff_self_inv _)

-- `simp` normal form of `Polynomial.degree_mul_leadingCoeff_self_inv`

