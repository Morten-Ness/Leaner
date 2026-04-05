import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {R : Type*} [Ring R] (r : R) (k : ℤ)

theorem intCast_mul_mem_zmultiples : ↑(k : ℤ) * r ∈ zmultiples r := by
  simpa only [← zsmul_eq_mul] using zsmul_mem_zmultiples r k

