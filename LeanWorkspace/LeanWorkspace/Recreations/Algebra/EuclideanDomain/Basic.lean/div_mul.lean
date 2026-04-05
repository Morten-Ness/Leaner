import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem div_mul {x y z : R} (h1 : y ∣ x) (h2 : y * z ∣ x) :
    x / (y * z) = x / y / z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [mul_zero, div_zero]
  apply EuclideanDomain.eq_div_of_mul_eq_right hz
  rw [← EuclideanDomain.mul_div_assoc z h2, mul_comm y z, EuclideanDomain.mul_div_mul_cancel hz h1]

