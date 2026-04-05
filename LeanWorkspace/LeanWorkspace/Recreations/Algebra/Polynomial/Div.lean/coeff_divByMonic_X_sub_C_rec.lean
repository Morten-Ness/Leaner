import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem coeff_divByMonic_X_sub_C_rec (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (Polynomial.X - Polynomial.C a)).coeff n = coeff p (n + 1) + a * (p /ₘ (Polynomial.X - Polynomial.C a)).coeff (n + 1) := by
  nontriviality R
  have := Polynomial.monic_X_sub_C a
  set q := p /ₘ (Polynomial.X - Polynomial.C a)
  rw [← Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C a)]
  have : degree (p %ₘ (Polynomial.X - Polynomial.C a)) < ↑(n + 1) := degree_X_sub_C a ▸ Polynomial.degree_modByMonic_lt p this
    |>.trans_le <| WithBot.coe_le_coe.mpr le_add_self
  simp [q, sub_mul, add_sub, coeff_eq_zero_of_degree_lt this]

