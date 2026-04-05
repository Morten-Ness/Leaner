import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [One M]

theorem mulSupport_min [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ min (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := Function.mulSupport_inf f g

