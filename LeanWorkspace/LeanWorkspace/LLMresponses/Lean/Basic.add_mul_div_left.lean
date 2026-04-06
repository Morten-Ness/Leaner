import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem add_mul_div_left (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) : (x + y * z) / y = x / y + z := by
  rcases h2 with ⟨w, rfl⟩
  rw [← mul_add]
  simp [h1]
