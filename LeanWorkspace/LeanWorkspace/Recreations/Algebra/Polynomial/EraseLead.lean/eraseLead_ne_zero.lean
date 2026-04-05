import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_ne_zero (f0 : 2 ≤ #f.support) : Polynomial.eraseLead f ≠ 0 := by
  rw [Ne, ← card_support_eq_zero, Polynomial.eraseLead_support]
  exact
    (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).ne.symm

