import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_curry₃ {γ : Type*} (f : α × β × γ → M) (h : HasFiniteMulSupport f) :
    ∏ᶠ abc, f abc = ∏ᶠ (a) (b) (c), f (a, b, c) := by
  rw [finprod_curry f h]
  congr
  ext a
  rw [finprod_curry]
  simp [h]

