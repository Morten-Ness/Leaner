import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem affineIndependent_iff_indicator_eq_of_affineCombination_eq (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s1 s2 : Finset ι) (w1 w2 : ι → k),
        ∑ i ∈ s1, w1 i = 1 →
          ∑ i ∈ s2, w2 i = 1 →
            s1.affineCombination k p w1 = s2.affineCombination k p w2 →
              Set.indicator (↑s1) w1 = Set.indicator (↑s2) w2 := by
  classical
    constructor
    · intro ha s1 s2 w1 w2 hw1 hw2 heq
      ext i
      by_cases hi : i ∈ s1 ∪ s2
      · rw [← sub_eq_zero]
        rw [← Finset.sum_indicator_subset w1 (s1.subset_union_left (s₂ := s2))] at hw1
        rw [← Finset.sum_indicator_subset w2 (s1.subset_union_right)] at hw2
        have hws : (∑ i ∈ s1 ∪ s2, (Set.indicator (↑s1) w1 - Set.indicator (↑s2) w2) i) = 0 := by
          simp [hw1, hw2]
        rw [Finset.affineCombination_indicator_subset w1 p (s1.subset_union_left (s₂ := s2)),
          Finset.affineCombination_indicator_subset w2 p s1.subset_union_right,
          ← @vsub_eq_zero_iff_eq V, Finset.affineCombination_vsub] at heq
        exact ha (s1 ∪ s2) (Set.indicator (↑s1) w1 - Set.indicator (↑s2) w2) hws heq i hi
      · simp_all
    · intro ha s w hw hs i0 hi0
      let w1 : ι → k := Function.update (Function.const ι 0) i0 1
      have hw1 : ∑ i ∈ s, w1 i = 1 := by
        rw [Finset.sum_update_of_mem hi0]
        simp only [Finset.sum_const_zero, add_zero, const_apply]
      have hw1s : s.affineCombination k p w1 = p i0 :=
        s.affineCombination_of_eq_one_of_eq_zero w1 p hi0 (Function.update_self ..)
          fun _ _ hne => Function.update_of_ne hne ..
      let w2 := w + w1
      have hw2 : ∑ i ∈ s, w2 i = 1 := by
        simp_all only [w2, Pi.add_apply, Finset.sum_add_distrib, zero_add]
      have hw2s : s.affineCombination k p w2 = p i0 := by
        simp_all only [w2, ← Finset.weightedVSub_vadd_affineCombination, zero_vadd]
      replace ha := ha s s w2 w1 hw2 hw1 (hw1s.symm ▸ hw2s)
      have hws : w2 i0 - w1 i0 = 0 := by
        rw [← Finset.mem_coe] at hi0
        rw [← Set.indicator_of_mem hi0 w2, ← Set.indicator_of_mem hi0 w1, ha, sub_self]
      simpa [w2] using hws

