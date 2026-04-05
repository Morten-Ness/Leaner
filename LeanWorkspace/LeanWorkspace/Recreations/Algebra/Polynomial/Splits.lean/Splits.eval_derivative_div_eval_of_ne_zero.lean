import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.eval_derivative_div_eval_of_ne_zero (hf : Polynomial.Splits f) {x : R} (hx : f.eval x ≠ 0) :
    f.derivative.eval x / f.eval x = (f.roots.map fun z ↦ 1 / (x - z)).sum := by
  rw [hf.eval_derivative_eq_eval_mul_sum hx, mul_div_cancel_left₀ _ hx]

