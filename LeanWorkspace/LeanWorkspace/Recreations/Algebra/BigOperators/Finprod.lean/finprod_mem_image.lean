import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_image {s : Set β} {g : β → α} (hg : s.InjOn g) :
    ∏ᶠ i ∈ g '' s, f i = ∏ᶠ j ∈ s, f (g j) := finprod_mem_image' <| hg.mono inter_subset_left

