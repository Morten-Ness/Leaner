import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_lt_iff_coeff_zero (f : R[X]) (n : ℕ) :
    Polynomial.degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 := by
  simp only [Polynomial.degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff,
    WithBot.coe_lt_coe, ← @not_le ℕ, max_eq_sup_coe, Nat.cast_withBot, Ne, not_imp_not]

