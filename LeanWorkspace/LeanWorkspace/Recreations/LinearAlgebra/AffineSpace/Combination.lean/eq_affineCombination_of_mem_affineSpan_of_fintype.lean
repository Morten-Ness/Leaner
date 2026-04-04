import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

theorem eq_affineCombination_of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι → P}
    (h : p1 ∈ affineSpan k (Set.range p)) :
    ∃ w : ι → k, ∑ i, w i = 1 ∧ p1 = Finset.univ.affineCombination k p w := by
  classical
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan h
    refine
      ⟨(s : Set ι).indicator w, ?_, Finset.affineCombination_indicator_subset w p s.subset_univ⟩
    simp only [Finset.mem_coe, Set.indicator_apply, ← hw]
    rw [Fintype.sum_extend_by_zero s w]

