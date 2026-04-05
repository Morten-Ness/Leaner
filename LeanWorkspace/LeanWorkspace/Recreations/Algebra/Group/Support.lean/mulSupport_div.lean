import Mathlib

variable {α M G : Type*}

variable [DivisionMonoid G] (f g : α → G)

theorem mulSupport_div : (mulSupport fun x => f x / g x) ⊆ mulSupport f ∪ mulSupport g := mulSupport_binop_subset (· / ·) one_div_one f g

