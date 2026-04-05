import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_erase [DecidableEq ι] (s : Finset ι) {f : ι → M} {a : ι} (h : f a = 1) :
    ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x := by
  rw [← sdiff_singleton_eq_erase]
  refine Finset.prod_subset sdiff_subset fun x hx hnx => ?_
  grind

