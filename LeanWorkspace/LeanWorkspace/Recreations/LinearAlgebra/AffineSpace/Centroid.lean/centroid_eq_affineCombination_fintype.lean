import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem centroid_eq_affineCombination_fintype [Fintype ι] (p : ι → P) :
    s.centroid k p = univ.affineCombination k p (s.centroidWeightsIndicator k) := affineCombination_indicator_subset _ _ (subset_univ _)

