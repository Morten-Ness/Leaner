import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem centroid_mem_affineSpan_of_cast_card_ne_zero {s : Finset ι} (p : ι → P)
    (h : (#s : k) ≠ 0) : s.centroid k p ∈ affineSpan k (Set.range p) := affineCombination_mem_affineSpan (Finset.sum_centroidWeights_eq_one_of_cast_card_ne_zero s h) p

