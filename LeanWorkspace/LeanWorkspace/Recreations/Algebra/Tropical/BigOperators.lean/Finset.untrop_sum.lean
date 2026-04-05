import Mathlib

variable {R S : Type*}

theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i ∈ s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [← untrop_sum _root_] using (sum_attach _ _).symm

