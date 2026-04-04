import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem lineMap_slope_lineMap_slope_lineMap (f : k → PE) (a b r : k) :
    lineMap (slope f (lineMap a b r) b) (slope f a (lineMap a b r)) r = slope f a b := by
  obtain rfl | hab : a = b ∨ a ≠ b := Classical.em _; · simp
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b]
  convert lineMap_slope_slope_sub_div_sub f b (lineMap a b r) a hab.symm using 2
  rw [lineMap_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]

