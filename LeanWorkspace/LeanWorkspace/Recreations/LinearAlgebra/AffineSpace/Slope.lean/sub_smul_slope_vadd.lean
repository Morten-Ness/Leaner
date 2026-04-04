import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem sub_smul_slope_vadd (f : k → PE) (a b : k) : (b - a) • slope f a b +ᵥ f a = f b := by
  rw [sub_smul_slope, vsub_vadd]

