import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_range' {g : β → α} (hg : (mulSupport (f ∘ g)).InjOn g) :
    ∏ᶠ i ∈ Set.range g, f i = ∏ᶠ j, f (g j) := by
  rw [← image_univ, finprod_mem_image', finprod_mem_univ]
  rwa [univ_inter]

