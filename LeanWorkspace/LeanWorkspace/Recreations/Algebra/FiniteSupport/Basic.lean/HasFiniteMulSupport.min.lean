import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.min [LinearOrder M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ min (f a) (g a) := (hf.union hg).subset <| mulSupport_min ..

