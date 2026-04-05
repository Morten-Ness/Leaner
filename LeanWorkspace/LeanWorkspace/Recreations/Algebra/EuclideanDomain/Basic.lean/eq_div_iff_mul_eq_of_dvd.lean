import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem eq_div_iff_mul_eq_of_dvd (x y z : R) (h1 : z ≠ 0) (h2 : z ∣ y) :
    x = y / z ↔ z * x = y := by
  rw [eq_comm, EuclideanDomain.div_eq_iff_eq_mul_of_dvd _ _ _ h1 h2, eq_comm]

