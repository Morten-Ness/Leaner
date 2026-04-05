import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem div_add_div_of_dvd {x y z t : R} (h1 : y ≠ 0) (h2 : t ≠ 0) (h3 : y ∣ x) (h4 : t ∣ z) :
    x / y + z / t = (t * x + y * z) / (t * y) := by
  apply EuclideanDomain.eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_add, mul_assoc, EuclideanDomain.mul_div_cancel' h1 h3, mul_comm t y,
    mul_assoc, EuclideanDomain.mul_div_cancel' h2 h4]

