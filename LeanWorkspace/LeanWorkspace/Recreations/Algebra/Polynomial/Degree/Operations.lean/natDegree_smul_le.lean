import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) :
    natDegree (a • p) ≤ natDegree p := natDegree_le_natDegree (Polynomial.degree_smul_le a p)

