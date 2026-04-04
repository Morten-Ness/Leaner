import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem affineIndependent_iff_of_fintype [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔
      ∀ w : ι → k, ∑ i, w i = 0 → Finset.univ.weightedVSub p w = (0 : V) → ∀ i, w i = 0 := by
  constructor
  · exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
  · intro h s w hw hs i hi
    rw [Finset.weightedVSub_indicator_subset _ _ (Finset.subset_univ s)] at hs
    rw [← Finset.sum_indicator_subset _ (Finset.subset_univ s)] at hw
    replace h := h ((↑s : Set ι).indicator w) hw hs i
    simpa [hi] using h

