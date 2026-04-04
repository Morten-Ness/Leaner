import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a := by
  rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]

