import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem sum_card_fiberwise_eq_card_filter {κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (g : ι → κ) : ∑ j ∈ t, #{i ∈ s | g i = j} = #{i ∈ s | g i ∈ t} := by
  simpa only [Finset.card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _

