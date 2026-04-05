import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem monic_of_degree_le (n : ℕ) (pn : p.degree ≤ n) (p1 : p.coeff n = 1) : Polynomial.Monic p := Polynomial.monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1

