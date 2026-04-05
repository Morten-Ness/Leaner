import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem mul_div_mul_cancel {a b c : R} (ha : a ≠ 0) (hcb : c ∣ b) : a * b / (a * c) = b / c := by
  by_cases hc : c = 0; · simp [hc]
  refine EuclideanDomain.eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha ?_)
  rw [← mul_assoc, ← EuclideanDomain.mul_div_assoc _ (by gcongr), mul_div_cancel_left₀ _ (mul_ne_zero ha hc)]

