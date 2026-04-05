import Mathlib

variable {R : Type*} [CommRing R] (r : R) (f : R[X])

theorem taylor_eval_sub (s : R) :
    (Polynomial.taylor r f).eval (s - r) = f.eval s := by rw [Polynomial.taylor_eval, sub_add_cancel]

