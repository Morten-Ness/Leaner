import Mathlib

variable {M α : Type*} [Small.{v} α]

theorem equivShrink_symm_one [One α] : (equivShrink α).symm 1 = 1 := (equivShrink α).symm_apply_apply 1

