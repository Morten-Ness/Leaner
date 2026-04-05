import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_mulSupport (f : α → M) : ∏ᶠ a ∈ mulSupport f, f a = ∏ᶠ a, f a := by
  rw [finprod_mem_def, mulIndicator_mulSupport]

