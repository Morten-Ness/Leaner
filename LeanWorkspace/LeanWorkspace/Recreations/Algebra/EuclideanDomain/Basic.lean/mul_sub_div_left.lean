import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem mul_sub_div_left (x y z : R) (h1 : z ≠ 0) (h2 : z ∣ y) : (z * x - y) / z = x - y / z := by
  rw [eq_comm]
  apply EuclideanDomain.eq_div_of_mul_eq_right h1
  rw [mul_sub, EuclideanDomain.mul_div_cancel' h1 h2]

