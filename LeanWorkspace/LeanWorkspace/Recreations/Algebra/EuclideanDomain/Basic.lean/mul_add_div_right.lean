import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem mul_add_div_right (x y z : R) (h1 : z ≠ 0) (h2 : z ∣ y) : (x * z + y) / z = x + y / z := by
  rw [mul_comm x z]
  exact EuclideanDomain.mul_add_div_left _ _ _ h1 h2

