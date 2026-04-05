import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ := ext fun _ => rfl

