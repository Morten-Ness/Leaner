import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.max [LinearOrder M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ max (f a) (g a) := (hf.union hg).subset <| mulSupport_max ..

