import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one [CharZero k] [Fintype ι] {n : ℕ}
    (h : #s = n + 1) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [Finset.sum_centroidWeightsIndicator]
  exact Finset.sum_centroidWeights_eq_one_of_card_eq_add_one s k h

