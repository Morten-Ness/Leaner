import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := ext fun n =>
    Nat.casesOn n (by simp) fun n =>
      Nat.casesOn n (by simp) fun m => by
        have : degree p < m.succ.succ := lt_of_le_of_lt h Nat.one_lt_ofNat
        simp [coeff_eq_zero_of_degree_lt this]

