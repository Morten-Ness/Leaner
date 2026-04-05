import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.eval_derivative_eq_eval_mul_sum (hf : Polynomial.Splits f) {x : R} (hx : f.eval x ≠ 0) :
    f.derivative.eval x = f.eval x * (f.roots.map fun z ↦ 1 / (x - z)).sum := by
  classical
  simp only [hf.eval_derivative, hf.eval_eq_prod_roots, ← Multiset.sum_map_mul_left, mul_assoc]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz ↦ ?_)
  rw [← Multiset.prod_map_erase hz, mul_one_div, mul_div_cancel_left₀]
  aesop (add simp sub_eq_zero)

