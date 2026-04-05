import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem natDegree_eq_natDegree {q : S[X]} (hpq : p.degree = q.degree) :
    p.natDegree = q.natDegree := by simp [natDegree, hpq]

