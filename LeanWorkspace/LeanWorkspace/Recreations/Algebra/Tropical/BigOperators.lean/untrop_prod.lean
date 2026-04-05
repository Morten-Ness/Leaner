import Mathlib

variable {R S : Type*}

theorem untrop_prod [AddCommMonoid R] (s : Finset S) (f : S → Tropical R) :
    untrop (∏ i ∈ s, f i) = ∑ i ∈ s, untrop (f i) := by
  convert Multiset.untrop_prod (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

