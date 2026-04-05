import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [One M]

theorem mulSupport_inf [SemilatticeInf M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊓ g x) ⊆ mulSupport f ∪ mulSupport g := mulSupport_binop_subset (· ⊓ ·) (inf_idem _) f g

