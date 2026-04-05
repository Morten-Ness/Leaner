import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree p) : p ≠ 0 := mt degree_eq_bot.2 h.ne_bot

