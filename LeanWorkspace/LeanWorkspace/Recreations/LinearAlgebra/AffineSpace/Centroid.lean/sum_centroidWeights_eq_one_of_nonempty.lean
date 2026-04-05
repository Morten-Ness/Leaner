import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem sum_centroidWeights_eq_one_of_nonempty [CharZero k] (h : s.Nonempty) :
    ∑ i ∈ s, s.centroidWeights k i = 1 := Finset.sum_centroidWeights_eq_one_of_card_ne_zero s k (ne_of_gt (card_pos.2 h))

