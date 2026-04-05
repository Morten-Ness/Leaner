import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_add_C (hp : 0 < degree p) : degree (p + Polynomial.C a) = degree p := add_comm (Polynomial.C a) p ▸ Polynomial.degree_add_eq_right_of_degree_lt <| lt_of_le_of_lt degree_C_le hp

