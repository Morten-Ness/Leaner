import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem eq_of_slope_eq_zero {f : k → PE} {a b : k} (h : slope f a b = (0 : E)) : f a = f b := by
  rw [← sub_smul_slope_vadd f a b, h, smul_zero, zero_vadd]

