import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y := by
  rw [lcm]; by_cases h : gcd x y = 0
  · rw [h, zero_mul]
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    rw [h.1, zero_mul]
  rcases EuclideanDomain.gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  generalize gcd x y = g at h hr ⊢; subst hr
  rw [mul_assoc, mul_div_cancel_left₀ _ h]

