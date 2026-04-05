import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.snd {M' : Type*} [One M'] {f : α → M × M'} (hf : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun a ↦ (f a).snd := hf.comp rfl

