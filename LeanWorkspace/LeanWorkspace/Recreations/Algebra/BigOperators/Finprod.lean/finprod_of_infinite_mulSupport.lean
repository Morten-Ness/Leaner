import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_of_infinite_mulSupport {f : α → M} (hf : (mulSupport f).Infinite) :
    ∏ᶠ i, f i = 1 := by
  classical
  rw [finprod_def]
  simp only [HasFiniteMulSupport]
  rw [dif_neg hf]

