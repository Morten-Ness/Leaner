import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (a⁻¹ * ·) := rfl

