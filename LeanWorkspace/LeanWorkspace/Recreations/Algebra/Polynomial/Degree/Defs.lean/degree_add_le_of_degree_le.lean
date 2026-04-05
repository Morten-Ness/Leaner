import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : Polynomial.degree p ≤ n) (hq : Polynomial.degree q ≤ n) :
    Polynomial.degree (p + q) ≤ n := (Polynomial.degree_add_le p q).trans <| max_le hp hq

