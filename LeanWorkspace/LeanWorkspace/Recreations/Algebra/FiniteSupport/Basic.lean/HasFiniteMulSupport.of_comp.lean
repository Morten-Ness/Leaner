import Mathlib

variable {α M : Type*} [One M]

variable {β : Type*} {f : β → M} {g : α → β}

theorem HasFiniteMulSupport.of_comp [One β] (hfg : (f ∘ g).HasFiniteMulSupport) (h : f 1 = 1)
    (hf : Function.Injective f) :
    g.HasFiniteMulSupport := by
  refine Set.Finite.subset hfg fun _ ha ↦ Set.mem_setOf.mpr fun H ↦ Set.mem_setOf.mp ha ?_
  grind

