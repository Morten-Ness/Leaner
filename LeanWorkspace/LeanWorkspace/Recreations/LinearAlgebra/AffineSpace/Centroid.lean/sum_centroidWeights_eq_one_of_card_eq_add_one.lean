import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem sum_centroidWeights_eq_one_of_card_eq_add_one [CharZero k] {n : ℕ} (h : #s = n + 1) :
    ∑ i ∈ s, s.centroidWeights k i = 1 := s.sum_centroidWeights_eq_one_of_card_ne_zero k (h.symm ▸ Nat.succ_ne_zero n)

