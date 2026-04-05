import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem le_natDegree_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : n ≤ p.natDegree := WithBot.coe_le_coe.mp <| by
    rwa [degree_eq_natDegree <| Polynomial.ne_zero_of_coe_le_degree hdeg] at hdeg

