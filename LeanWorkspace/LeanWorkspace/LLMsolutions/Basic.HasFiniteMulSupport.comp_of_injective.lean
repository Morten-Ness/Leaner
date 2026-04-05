FAIL
import Mathlib

variable {α M : Type*} [One M]

variable {β : Type*} {f : β → M} {g : α → β}

theorem HasFiniteMulSupport.comp_of_injective (hg : Function.Injective g) (hf : f.HasFiniteMulSupport) :
    (f ∘ g).HasFiniteMulSupport := by
  classical
  simpa [Function.mulSupport_comp_eq_preimage, hg] using hf.preimage hg
