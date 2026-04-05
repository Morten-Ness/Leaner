import Mathlib

variable {R S : Type*}

theorem trop_sum [AddCommMonoid R] (s : Finset S) (f : S → R) :
    trop (∑ i ∈ s, f i) = ∏ i ∈ s, trop (f i) := by
  convert Multiset.trop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

