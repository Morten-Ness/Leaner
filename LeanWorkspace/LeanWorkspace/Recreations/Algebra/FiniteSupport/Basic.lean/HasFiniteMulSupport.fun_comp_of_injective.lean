import Mathlib

variable {α M : Type*} [One M]

variable {β : Type*} {f : β → M} {g : α → β}

theorem HasFiniteMulSupport.fun_comp_of_injective (hg : Function.Injective g) (hf : f.HasFiniteMulSupport) :
    (fun a ↦ f (g a)).HasFiniteMulSupport := hf.comp_of_injective hg

