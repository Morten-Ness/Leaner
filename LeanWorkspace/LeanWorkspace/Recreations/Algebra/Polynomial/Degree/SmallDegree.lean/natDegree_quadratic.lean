import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_quadratic (ha : a ≠ 0) : natDegree (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) = 2 := natDegree_eq_of_degree_eq_some <| Polynomial.degree_quadratic ha

