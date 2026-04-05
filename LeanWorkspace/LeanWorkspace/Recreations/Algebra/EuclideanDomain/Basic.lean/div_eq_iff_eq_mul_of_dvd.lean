import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem div_eq_iff_eq_mul_of_dvd (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) :
    x / y = z ↔ x = y * z := by
  obtain ⟨a, ha⟩ := h2
  rw [ha, mul_div_cancel_left₀ _ h1]
  simp only [mul_eq_mul_left_iff, h1, or_false]

