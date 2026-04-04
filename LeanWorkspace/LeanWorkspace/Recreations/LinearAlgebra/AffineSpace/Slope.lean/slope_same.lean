import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 := by
  rw [slope, sub_self, inv_zero, zero_smul]

