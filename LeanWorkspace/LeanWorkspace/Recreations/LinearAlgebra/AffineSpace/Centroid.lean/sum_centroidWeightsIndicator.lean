import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem sum_centroidWeightsIndicator [Fintype ι] :
    ∑ i, s.centroidWeightsIndicator k i = ∑ i ∈ s, s.centroidWeights k i := sum_indicator_subset _ (subset_univ _)

