import Mathlib

variable {α M G : Type*}

variable [DivisionMonoid G] (f g : α → G)

theorem mulSupport_fun_inv : (mulSupport fun x => (f x)⁻¹) = mulSupport f := ext fun _ => inv_ne_one

