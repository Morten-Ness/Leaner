import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 := Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])) hpq :
      q.degree > ⊥)

