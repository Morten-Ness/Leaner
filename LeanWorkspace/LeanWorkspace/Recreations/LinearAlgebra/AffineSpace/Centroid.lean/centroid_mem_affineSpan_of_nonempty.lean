import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable (k)

theorem centroid_mem_affineSpan_of_nonempty [CharZero k] {s : Finset ι} (p : ι → P)
    (h : s.Nonempty) : s.centroid k p ∈ affineSpan k (Set.range p) := affineCombination_mem_affineSpan (Finset.sum_centroidWeights_eq_one_of_nonempty s k h) p

