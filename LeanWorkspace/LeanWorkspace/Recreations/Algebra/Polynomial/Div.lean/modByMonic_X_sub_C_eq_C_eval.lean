import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem modByMonic_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p %ₘ (Polynomial.X - Polynomial.C a) = Polynomial.C (p.eval a) := by
  nontriviality R
  have h : (p %ₘ (Polynomial.X - Polynomial.C a)).eval a = p.eval a := by
    rw [Polynomial.modByMonic_eq_sub_mul_div, eval_sub, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, sub_zero]
  have : degree (p %ₘ (Polynomial.X - Polynomial.C a)) < 1 :=
    degree_X_sub_C a ▸ Polynomial.degree_modByMonic_lt p (Polynomial.monic_X_sub_C a)
  have : degree (p %ₘ (Polynomial.X - Polynomial.C a)) ≤ 0 := by
    revert this
    cases degree (p %ₘ (Polynomial.X - Polynomial.C a))
    · exact fun _ => bot_le
    · exact fun h => WithBot.coe_le_coe.2 (Nat.le_of_lt_succ (WithBot.coe_lt_coe.1 h))
  rw [eq_C_of_degree_le_zero this, eval_C] at h
  rw [eq_C_of_degree_le_zero this, h]

