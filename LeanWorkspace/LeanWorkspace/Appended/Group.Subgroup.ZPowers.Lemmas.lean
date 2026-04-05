import Mathlib

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {R : Type*} [Ring R] (r : R) (k : ℤ)

theorem intCast_mul_mem_zmultiples : ↑(k : ℤ) * r ∈ zmultiples r := by
  simpa only [← zsmul_eq_mul] using zsmul_mem_zmultiples r k

end

section

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem range_nsmulAddMonoidHom (n : ℕ) : (nsmulAddMonoidHom n).range = zmultiples (n : ℤ) := by
  ext m : 1
  simp [mem_zmultiples_iff, dvd_def]
  grind

end
