import Mathlib

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem det_one_add_X_smul (M : Matrix n n R) :
    det (1 + (Polynomial.X : R[Polynomial.X]) • M.map Polynomial.C) =
      (1 : R[Polynomial.X]) + trace M • Polynomial.X + (det (1 + (Polynomial.X : R[Polynomial.X]) • M.map Polynomial.C)).divX.divX * Polynomial.X ^ 2 := by
  rw [Algebra.smul_def (trace M), ← C_eq_algebraMap, pow_two, ← mul_assoc, add_assoc,
    ← add_mul, ← Matrix.coeff_det_one_add_X_smul_one, ← coeff_divX, add_comm (Polynomial.C _), divX_mul_X_add,
    add_comm (1 : R[Polynomial.X]), ← Polynomial.C.map_one]
  convert (divX_mul_X_add _).symm
  rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]

