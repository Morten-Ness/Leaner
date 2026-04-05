import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M}
    (H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b} := by
  simp only [Finset.card_eq_sum_ones, sum_fiberwise_of_maps_to H]

