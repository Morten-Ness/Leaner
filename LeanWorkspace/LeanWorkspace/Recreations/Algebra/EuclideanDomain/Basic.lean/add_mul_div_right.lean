import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem add_mul_div_right (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) : (x + z * y) / y = x / y + z := by
  rw [mul_comm z y]
  exact EuclideanDomain.add_mul_div_left _ _ _ h1 h2

