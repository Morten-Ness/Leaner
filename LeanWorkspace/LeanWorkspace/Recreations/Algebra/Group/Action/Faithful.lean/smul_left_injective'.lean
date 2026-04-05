import Mathlib

variable {M G α : Type*}

theorem smul_left_injective' [SMul M α] [FaithfulSMul M α] : Function.Injective ((· • ·) : M → α → α) := fun _ _ h ↦ FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)

