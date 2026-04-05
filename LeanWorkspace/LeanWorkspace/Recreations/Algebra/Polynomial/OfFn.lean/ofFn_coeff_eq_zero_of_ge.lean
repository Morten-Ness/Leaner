import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem ofFn_coeff_eq_zero_of_ge {n i : ℕ} (v : Fin n → R) (hi : n ≤ i) :
    (Polynomial.ofFn n v).coeff i = 0 := by
  simp [Polynomial.ofFn, Nat.not_lt_of_ge hi]

