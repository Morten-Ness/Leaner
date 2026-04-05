import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_C_lt : Polynomial.degree (Polynomial.C a) < 1 := Polynomial.degree_C_le.trans_lt <| WithBot.coe_lt_coe.mpr zero_lt_one

