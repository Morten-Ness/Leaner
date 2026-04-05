import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_linear_lt : degree (Polynomial.C a * Polynomial.X + Polynomial.C b) < 2 := Polynomial.degree_linear_le.trans_lt <| WithBot.coe_lt_coe.mpr one_lt_two

