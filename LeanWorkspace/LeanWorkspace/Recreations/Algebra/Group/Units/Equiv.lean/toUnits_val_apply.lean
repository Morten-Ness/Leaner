import Mathlib

variable {F α M N G : Type*}

theorem toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x := by
  simp_rw [MulEquiv.apply_eq_iff_symm_apply, toUnits_symm_apply]

