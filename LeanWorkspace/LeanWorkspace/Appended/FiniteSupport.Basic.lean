import Mathlib

section

variable {α M : Type*} [One M]

variable {β : Type*} {f : β → M} {g : α → β}

theorem HasFiniteMulSupport.comp_of_injective (hg : Function.Injective g) (hf : f.HasFiniteMulSupport) :
    (f ∘ g).HasFiniteMulSupport := by
  refine Set.Finite.of_injOn ?_ (Set.injOn_of_injective hg) hf
  grind [Set.mapsTo_iff_subset_preimage]

end

section

variable {α M : Type*} [One M]

variable {β : Type*} {f : β → M} {g : α → β}

theorem HasFiniteMulSupport.of_comp [One β] (hfg : (f ∘ g).HasFiniteMulSupport) (h : f 1 = 1)
    (hf : Function.Injective f) :
    g.HasFiniteMulSupport := by
  refine Set.Finite.subset hfg fun _ ha ↦ Set.mem_setOf.mpr fun H ↦ Set.mem_setOf.mp ha ?_
  grind

end
