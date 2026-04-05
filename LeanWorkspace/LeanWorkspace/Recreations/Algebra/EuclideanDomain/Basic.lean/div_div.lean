import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem div_div {x y z : R} (h1 : y ∣ x) (h2 : z ∣ (x / y)) :
    x / y / z = x / (y * z) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [div_zero, EuclideanDomain.zero_div, zero_mul]
  rw [← mul_dvd_mul_iff_left hy, EuclideanDomain.mul_div_cancel' hy h1] at h2
  exact (EuclideanDomain.div_mul h1 h2).symm

