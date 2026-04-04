import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem affineIndependent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔ ∀ w1 w2 : ι → k, ∑ i, w1 i = 1 → ∑ i, w2 i = 1 →
    Finset.univ.affineCombination k p w1 = Finset.univ.affineCombination k p w2 → w1 = w2 := by
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
  constructor
  · intro h w1 w2 hw1 hw2 hweq
    simpa only [Set.indicator_univ, Finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq
  · intro h s1 s2 w1 w2 hw1 hw2 hweq
    have hw1' : (∑ i, (s1 : Set ι).indicator w1 i) = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s1)]
    have hw2' : (∑ i, (s2 : Set ι).indicator w2 i) = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s2)]
    rw [Finset.affineCombination_indicator_subset w1 p (Finset.subset_univ s1),
      Finset.affineCombination_indicator_subset w2 p (Finset.subset_univ s2)] at hweq
    exact h _ _ hw1' hw2' hweq

