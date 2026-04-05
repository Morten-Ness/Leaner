import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R]

theorem degree_neg_le_of_le {a : WithBot ℕ} {p : R[X]} (hp : Polynomial.degree p ≤ a) : Polynomial.degree (-p) ≤ a := Polynomial.degree_neg p.le.trans hp

