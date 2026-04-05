import Mathlib

variable {α M G : Type*}

theorem mulSupport_mul [MulOneClass M] (f g : α → M) :
    (mulSupport fun x ↦ f x * g x) ⊆ mulSupport f ∪ mulSupport g := mulSupport_binop_subset (· * ·) (one_mul _) f g

