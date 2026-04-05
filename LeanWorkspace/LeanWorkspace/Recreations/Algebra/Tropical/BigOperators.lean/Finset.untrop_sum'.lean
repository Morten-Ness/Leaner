import Mathlib

variable {R S : Type*}

theorem Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → Tropical R) :
    untrop (∑ i ∈ s, f i) = s.inf (untrop ∘ f) := by
  convert Multiset.untrop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply, inf_def]

