import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_cubic_lt : degree (Polynomial.C a * Polynomial.X ^ 3 + Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X + Polynomial.C d) < 4 := Polynomial.degree_cubic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 3

