import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem ofFn_coeff_eq_val_of_lt {n i : ℕ} (v : Fin n → R) (hi : i < n) :
    (Polynomial.ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [Polynomial.ofFn, hi]

