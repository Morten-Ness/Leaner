import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = Polynomial.C (coeff p 0) := by
  ext (_ | n)
  · simp
  rw [coeff_C, if_neg (Nat.succ_ne_zero _), Polynomial.coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)

