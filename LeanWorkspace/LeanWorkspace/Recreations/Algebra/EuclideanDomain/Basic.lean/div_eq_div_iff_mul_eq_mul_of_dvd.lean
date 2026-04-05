import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem div_eq_div_iff_mul_eq_mul_of_dvd {x y z t : R} (h1 : y ≠ 0) (h2 : t ≠ 0)
    (h3 : y ∣ x) (h4 : t ∣ z) : x / y = z / t ↔ t * x = y * z := by
  rw [EuclideanDomain.div_eq_iff_eq_mul_of_dvd _ _ _ h1 h3, ← EuclideanDomain.mul_div_assoc _ h4,
    EuclideanDomain.eq_div_iff_mul_eq_of_dvd _ _ _ h2]
  obtain ⟨a, ha⟩ := h4
  use y * a
  rw [ha, mul_comm, mul_assoc, mul_comm y a]

