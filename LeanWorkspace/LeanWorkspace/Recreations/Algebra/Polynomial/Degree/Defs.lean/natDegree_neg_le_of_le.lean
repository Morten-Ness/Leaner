import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem natDegree_neg_le_of_le {p : R[X]} (hp : Polynomial.natDegree p ≤ m) : Polynomial.natDegree (-p) ≤ m := (Polynomial.natDegree_neg p).le.trans hp

