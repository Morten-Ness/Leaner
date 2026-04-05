import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ := ext fun _ => rfl

