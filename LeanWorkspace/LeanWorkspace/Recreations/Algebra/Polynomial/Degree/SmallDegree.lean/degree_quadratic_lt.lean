import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_quadratic_lt : degree (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) < 3 := Polynomial.degree_quadratic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 2

