import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_apply_ne_one (f : α → M) (a : α) : ∏ᶠ _ : f a ≠ 1, f a = f a := by
  rw [← mem_mulSupport, finprod_eq_mulIndicator_apply, mulIndicator_mulSupport]

