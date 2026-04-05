import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_single (f : α → M) (a : α) (ha : ∀ x, x ≠ a → f x = 1) :
    ∏ᶠ x, f x = f a := by
  have : mulSupport (f ∘ PLift.down) ⊆ ({PLift.up a} : Finset (PLift α)) := by
    intro x
    contrapose
    simpa [PLift.eq_up_iff_down_eq] using ha x.down
  rw [finprod_eq_prod_plift_of_mulSupport_subset this, Finset.prod_singleton]

