import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_eq_one_of_infinite {f : α → M} {s : Set α} (hs : (s ∩ mulSupport f).Infinite) :
    ∏ᶠ i ∈ s, f i = 1 := by
  rw [finprod_mem_def]
  apply finprod_of_infinite_mulSupport
  rwa [← mulSupport_mulIndicator] at hs

