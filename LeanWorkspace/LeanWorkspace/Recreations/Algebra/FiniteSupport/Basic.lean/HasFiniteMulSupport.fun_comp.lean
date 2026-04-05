import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.fun_comp {N : Type*} [One N] {g : M → N} {f : α → M}
    (hf : HasFiniteMulSupport f) (hg : g 1 = 1) :
    HasFiniteMulSupport fun a ↦ g (f a) := hf.subset <| mulSupport_comp_subset hg f

