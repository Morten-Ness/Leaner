import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem mul_divByMonic_cancel_left (p : R[X]) {q : R[X]} (hmo : q.Monic) :
    q * p /ₘ q = p := by
  nontriviality R
  refine (Polynomial.div_modByMonic_unique _ 0 hmo ⟨by rw [zero_add], ?_⟩).1
  rw [degree_zero]
  exact Ne.bot_lt fun h => hmo.ne_zero (degree_eq_bot.1 h)

