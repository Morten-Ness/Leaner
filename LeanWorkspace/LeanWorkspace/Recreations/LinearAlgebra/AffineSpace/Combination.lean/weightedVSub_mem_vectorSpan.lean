import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem weightedVSub_mem_vectorSpan {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0)
    (p : ι → P) : s.weightedVSub p w ∈ vectorSpan k (Set.range p) := by
  classical
    rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
    · simp [Finset.eq_empty_of_isEmpty s]
    · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
        Finsupp.mem_span_image_iff_linearCombination,
        Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p h (p i0),
        Finset.weightedVSubOfPoint_apply]
      let w' := Set.indicator (↑s) w
      have hwx : ∀ i, w' i ≠ 0 → i ∈ s := fun i => Set.mem_of_indicator_ne_zero
      use Finsupp.onFinset s w' hwx, Set.subset_univ _
      rw [Finsupp.linearCombination_apply, Finsupp.onFinset_sum hwx]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [w', Set.indicator_apply, if_pos hi]
      · exact fun _ => zero_smul k _

