import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ := rfl

