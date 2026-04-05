import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_eq_iff_natDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.degree = n ↔ p.natDegree = n := by rw [Polynomial.degree_eq_natDegree hp]; exact WithBot.coe_eq_coe

