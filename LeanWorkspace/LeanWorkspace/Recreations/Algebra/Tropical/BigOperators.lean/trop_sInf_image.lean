import Mathlib

variable {R S : Type*}

theorem trop_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → WithTop R) :
    trop (sInf (f '' s)) = ∑ i ∈ s, trop (f i) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, trop_top]
  rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, s.trop_inf]

