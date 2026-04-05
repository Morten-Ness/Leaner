import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_ne_of_natDegree_ne {n : ℕ} : p.natDegree ≠ n → Polynomial.degree p ≠ n := mt Polynomial.natDegree_eq_of_degree_eq_some

