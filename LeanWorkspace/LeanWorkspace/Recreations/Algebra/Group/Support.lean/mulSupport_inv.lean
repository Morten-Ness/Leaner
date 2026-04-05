import Mathlib

variable {α M G : Type*}

variable [DivisionMonoid G] (f g : α → G)

theorem mulSupport_inv : mulSupport f⁻¹ = mulSupport f := Function.mulSupport_fun_inv f

