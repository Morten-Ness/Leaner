import Mathlib

variable {R S : Type*}

theorem Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → R) :
    trop (s.inf f) = ∑ i ∈ s, trop (f i) := by
  convert Multiset.trop_inf (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

