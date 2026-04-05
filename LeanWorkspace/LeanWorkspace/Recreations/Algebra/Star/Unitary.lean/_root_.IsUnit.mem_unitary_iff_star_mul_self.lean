import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem _root_.IsUnit.mem_unitary_iff_star_mul_self {u : R} (hu : IsUnit u) :
    u ∈ unitary R ↔ star u * u = 1 := by
  rw [Unitary.mem_iff, and_iff_left_of_imp fun h_mul => ?_]
  lift u to Rˣ using hu
  exact left_inv_eq_right_inv h_mul u.mul_inv ▸ u.mul_inv

