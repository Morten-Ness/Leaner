import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem supDegree_eq_degree (p : R[X]) : p.toFinsupp.supDegree WithBot.some = p.degree := max_eq_sup_coe

