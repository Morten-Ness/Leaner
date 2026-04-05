import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem mul_inv_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) :
    a * b⁻¹ ∈ unitary G ↔ star a * a = star b * b := by
  rw [(Group.isUnit _).mem_unitary_iff_star_mul_self, star_mul, star_inv, mul_assoc,
    inv_mul_eq_iff_eq_mul, mul_one, ← mul_assoc, mul_inv_eq_iff_eq_mul]

