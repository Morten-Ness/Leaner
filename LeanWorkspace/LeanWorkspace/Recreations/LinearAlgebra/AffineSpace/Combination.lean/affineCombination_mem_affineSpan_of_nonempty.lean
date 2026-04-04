import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem affineCombination_mem_affineSpan_of_nonempty [Nonempty ι] {s : Finset ι} {w : ι → k}
    (h : ∑ i ∈ s, w i = 1) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (Set.range p) := by
  rcases subsingleton_or_nontrivial k with hs | hn
  · have hnv := Module.subsingleton k V
    rw [AddTorsor.subsingleton_iff V P] at hnv
    rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (Set.range_nonempty p)]
    simp
  · exact affineCombination_mem_affineSpan h p

