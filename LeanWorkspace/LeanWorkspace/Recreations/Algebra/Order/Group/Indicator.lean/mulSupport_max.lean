import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [One M]

theorem mulSupport_max [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ max (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := Function.mulSupport_sup f g

