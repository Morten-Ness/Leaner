import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable (k V)

variable {V}

variable {k}

theorem AffineIndependent.affineIndependent_of_notMem_span {p : ι → P} {i : ι}
    (ha : AffineIndependent k fun x : { y // y ≠ i } => p x)
    (hi : p i ∉ affineSpan k (p '' { x | x ≠ i })) : AffineIndependent k p := by
  classical
    intro s w hw hs
    let s' : Finset { y // y ≠ i } := s.subtype (· ≠ i)
    let p' : { y // y ≠ i } → P := fun x => p x
    by_cases his : i ∈ s ∧ w i ≠ 0
    · refine False.elim (hi ?_)
      let wm : ι → k := -(w i)⁻¹ • w
      have hms : s.weightedVSub p wm = (0 : V) := by simp [wm, hs]
      have hwm : ∑ i ∈ s, wm i = 0 := by simp [wm, ← Finset.mul_sum, hw]
      have hwmi : wm i = -1 := by simp [wm, his.2]
      let w' : { y // y ≠ i } → k := fun x => wm x
      have hw' : ∑ x ∈ s', w' x = 1 := by
        simp_rw [w', s', Finset.sum_subtype_eq_sum_filter]
        rw [← s.sum_filter_add_sum_filter_not (· ≠ i)] at hwm
        simpa only [not_not, Finset.filter_eq' _ i, if_pos his.1, sum_singleton, hwmi,
          add_neg_eq_zero] using hwm
      rw [← s.affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one hms his.1 hwmi, ←
        (Subtype.range_coe : _ = { x | x ≠ i }), ← Set.range_comp, ←
        s.affineCombination_subtype_eq_filter]
      exact affineCombination_mem_affineSpan hw' p'
    · rw [not_and_or, Classical.not_not] at his
      let w' : { y // y ≠ i } → k := fun x => w x
      have hw' : ∑ x ∈ s', w' x = 0 := by
        simp_rw [w', s', Finset.sum_subtype_eq_sum_filter]
        rw [Finset.sum_filter_of_ne, hw]
        rintro x hxs hwx rfl
        exact hwx (his.neg_resolve_left hxs)
      have hs' : s'.weightedVSub p' w' = (0 : V) := by
        simp_rw [w', s', p', Finset.weightedVSub_subtype_eq_filter]
        rw [Finset.weightedVSub_filter_of_ne, hs]
        rintro x hxs hwx rfl
        exact hwx (his.neg_resolve_left hxs)
      intro j hj
      by_cases hji : j = i
      · rw [hji] at hj
        exact hji.symm ▸ his.neg_resolve_left hj
      · exact ha s' w' hw' hs' ⟨j, hji⟩ (Finset.mem_subtype.2 hj)

