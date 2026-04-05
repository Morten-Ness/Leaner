import Mathlib

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

theorem taylor_eval (r : R) (f : R[X]) (s : R) : (Polynomial.taylor r f).eval s = f.eval (s + r) := by
  simp only [Polynomial.taylor_apply, eval_comp, eval_C, eval_X, eval_add]

