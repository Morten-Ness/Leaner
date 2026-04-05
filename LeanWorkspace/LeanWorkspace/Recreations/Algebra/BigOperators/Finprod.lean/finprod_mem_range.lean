import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_range {g : β → α} (hg : Function.Injective g) : ∏ᶠ i ∈ Set.range g, f i = ∏ᶠ j, f (g j) := finprod_mem_range' hg.injOn

