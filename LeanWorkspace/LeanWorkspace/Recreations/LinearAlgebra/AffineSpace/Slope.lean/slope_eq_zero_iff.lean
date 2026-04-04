import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_eq_zero_iff {f : k → E} {a b : k} : slope f a b = 0 ↔ f a = f b := by
  simp [slope, sub_eq_zero, eq_comm, or_iff_right_of_imp (congr_arg _)]

