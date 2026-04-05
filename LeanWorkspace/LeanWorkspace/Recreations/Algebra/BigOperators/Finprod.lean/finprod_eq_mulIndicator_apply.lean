import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_mulIndicator_apply (s : Set α) (f : α → M) (a : α) :
    ∏ᶠ _ : a ∈ s, f a = mulIndicator s f a := by
  classical convert finprod_eq_if (M := M) (p := a ∈ s) (x := f a)

