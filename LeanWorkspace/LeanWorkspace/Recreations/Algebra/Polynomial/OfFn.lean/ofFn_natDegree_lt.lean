import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem ofFn_natDegree_lt {n : ℕ} (h : 1 ≤ n) (v : Fin n → R) : (Polynomial.ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h, natDegree_le_iff_coeff_eq_zero]
  exact fun _ h ↦ Polynomial.ofFn_coeff_eq_zero_of_ge _ <| Nat.le_of_pred_lt h

