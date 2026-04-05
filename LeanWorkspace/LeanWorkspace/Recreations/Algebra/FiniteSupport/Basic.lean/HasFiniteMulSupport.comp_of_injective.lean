import Mathlib

variable {α M : Type*} [One M]

variable {β : Type*} {f : β → M} {g : α → β}

theorem HasFiniteMulSupport.comp_of_injective (hg : Function.Injective g) (hf : f.HasFiniteMulSupport) :
    (f ∘ g).HasFiniteMulSupport := by
  refine Set.Finite.of_injOn ?_ (Set.injOn_of_injective hg) hf
  grind [Set.mapsTo_iff_subset_preimage]

