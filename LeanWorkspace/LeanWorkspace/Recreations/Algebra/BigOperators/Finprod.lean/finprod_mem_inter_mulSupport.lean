import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_inter_mulSupport (f : α → M) (s : Set α) :
    ∏ᶠ i ∈ s ∩ mulSupport f, f i = ∏ᶠ i ∈ s, f i := by
  rw [finprod_mem_def, finprod_mem_def, mulIndicator_inter_mulSupport]

