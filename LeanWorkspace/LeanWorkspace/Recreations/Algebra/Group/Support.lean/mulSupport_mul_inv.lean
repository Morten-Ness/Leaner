import Mathlib

variable {α M G : Type*}

variable [DivisionMonoid G] (f g : α → G)

theorem mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) ⊆ mulSupport f ∪ mulSupport g := mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g

