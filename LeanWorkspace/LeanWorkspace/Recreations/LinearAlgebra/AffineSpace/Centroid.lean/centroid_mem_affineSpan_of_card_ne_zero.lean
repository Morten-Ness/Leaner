import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable (k)

theorem centroid_mem_affineSpan_of_card_ne_zero [CharZero k] {s : Finset ι} (p : ι → P)
    (h : #s ≠ 0) : s.centroid k p ∈ affineSpan k (Set.range p) := affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_ne_zero k h) p

