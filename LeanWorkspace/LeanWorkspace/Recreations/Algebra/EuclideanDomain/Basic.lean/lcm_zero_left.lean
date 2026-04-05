import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem lcm_zero_left (x : R) : lcm 0 x = 0 := by rw [lcm, zero_mul, EuclideanDomain.zero_div]

