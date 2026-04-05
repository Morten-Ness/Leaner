import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_eq_one_of_forall_eq_one {f : α → M} (h : ∀ x, f x = 1) : ∏ᶠ i, f i = 1 := by
  simp +contextual [h]

