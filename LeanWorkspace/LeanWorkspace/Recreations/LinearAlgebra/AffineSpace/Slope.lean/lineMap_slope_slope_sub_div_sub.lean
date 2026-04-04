import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem lineMap_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
    lineMap (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c := by
  simp only [lineMap_apply_module, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
    add_left_inj]
  match_scalars
  field [sub_ne_zero.2 h.symm]

