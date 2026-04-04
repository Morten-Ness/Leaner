import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem sub_smul_slope (f : k → PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f a := by
  rcases eq_or_ne a b with (rfl | hne)
  · rw [sub_self, zero_smul, vsub_self]
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]

