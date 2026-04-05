import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem Finset.mulSupport_of_fiberwise_prod_subset_image [DecidableEq β] (s : Finset α) (f : α → M)
    (g : α → β) : (mulSupport fun b ↦ ∏ a ∈ s with g a = b, f a) ⊆ s.image g := by
  simp only [Finset.coe_image]
  intro b h
  suffices {a ∈ s | g a = b}.Nonempty by
    simpa only [fiber_nonempty_iff_mem_image, Finset.mem_image, exists_prop]
  exact Finset.nonempty_of_prod_ne_one h

