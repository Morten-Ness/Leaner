import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_sub_le_of_le {a b : WithBot ℕ} (hp : Polynomial.degree p ≤ a) (hq : Polynomial.degree q ≤ b) :
    Polynomial.degree (p - q) ≤ max a b := (Polynomial.degree_sub_le p q).trans <| max_le_max ‹_› ‹_›

