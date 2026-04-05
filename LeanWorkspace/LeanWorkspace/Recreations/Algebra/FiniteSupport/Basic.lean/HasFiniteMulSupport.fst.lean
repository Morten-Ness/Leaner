import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.fst {M' : Type*} [One M'] {f : α → M × M'} (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).fst := hf.comp rfl

