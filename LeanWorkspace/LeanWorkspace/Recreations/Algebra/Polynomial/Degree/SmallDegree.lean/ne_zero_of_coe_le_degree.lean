import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem ne_zero_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : p ≠ 0 := Polynomial.zero_le_degree_iff.mp <| (WithBot.coe_le_coe.mpr n.zero_le).trans hdeg

