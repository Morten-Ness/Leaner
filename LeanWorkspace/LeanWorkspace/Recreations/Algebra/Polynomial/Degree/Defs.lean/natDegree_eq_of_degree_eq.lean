import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_eq_of_degree_eq [Semiring S] {q : S[X]} (h : Polynomial.degree p = Polynomial.degree q) :
    Polynomial.natDegree p = Polynomial.natDegree q := by unfold Polynomial.natDegree; rw [h]

