import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_mul_diff' (hst : s ⊆ t) (ht : (t ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mul_diff' _ ht, inter_eq_self_of_subset_right hst]

