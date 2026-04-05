import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_of_isEmpty [IsEmpty α] (f : α → M) : ∏ᶠ i, f i = 1 := by
  rw [← finprod_one]
  congr
  simp [eq_iff_true_of_subsingleton]

