import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem X_pow_add_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (Polynomial.X : R[X]) ^ n + Polynomial.C a ≠ 0 := mt degree_eq_bot.2
    (show degree ((Polynomial.X : R[X]) ^ n + Polynomial.C a) ≠ ⊥ by
      rw [Polynomial.degree_X_pow_add_C hn a]; exact WithBot.coe_ne_bot)

