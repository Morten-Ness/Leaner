import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem coeff_det_one_add_X_smul_one (M : Matrix n n R) :
    (det (1 + (Polynomial.X : R[Polynomial.X]) • M.map Polynomial.C)).coeff 1 = trace M := by
  simp only [← Matrix.derivative_det_one_add_X_smul, ← coeff_zero_eq_eval_zero,
    coeff_derivative, zero_add, Nat.cast_zero, mul_one]

