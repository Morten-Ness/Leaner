import Mathlib

variable {R S : Type*}

theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [iInf, ← Set.image_univ, ← coe_univ, untrop_sum_eq_sInf_image, Function.comp_def]

