import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem inv_mul_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) :
    a⁻¹ * b ∈ unitary G ↔ a * star a = b * star b := by
  simpa [← mul_inv_rev] using Unitary.mul_inv_mem_iff a⁻¹ b⁻¹

