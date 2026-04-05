import Mathlib

variable {k V P ι : Type*}

variable [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

private theorem exists_affineCombination_eq_smul_eq_aux {p : ι → P} (hp : AffineIndependent k p)
    {s : Set ι} (hs : s.Nonempty) {fs : s → Finset ι} (hfs : ∀ i, (i : ι) ∈ fs i) {w : s → ι → k}
    (hw : ∀ i, ∑ j ∈ fs i, w i j = 1) {p' : P}
    (hp' : ∀ i : s, p' ∈ line[k, p i, (fs i).affineCombination k p (w i)]) :
    ∃ (w' : ι → k) (fs' : Finset ι), (∑ j ∈ fs', w' j = 1) ∧ fs'.affineCombination k p w' = p' ∧
      ∀ i : s, ∃ r, ∀ j, r * Set.indicator ((fs i : Set ι) \ {(i : ι)}) (w i) j =
        Set.indicator ((fs' : Set ι) \ {(i : ι)}) w' j := by
  classical
  have hp'' : ∀ i : s, ∃ r : k, (fs i).affineCombination k p
      (AffineMap.lineMap (Finset.affineCombinationSingleWeights k (i : ι)) (w i) r) = p' := by
    intro i
    simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp'
    obtain ⟨r, rfl⟩ := hp' i
    exact ⟨r, by simp [hfs]⟩
  obtain ⟨i', hi'⟩ := hs
  obtain ⟨ri', hri'⟩ := hp'' ⟨i', hi'⟩
  let w' : ι → k :=
    AffineMap.lineMap (Finset.affineCombinationSingleWeights k i') (w ⟨i', hi'⟩) ri'
  refine ⟨w', fs ⟨i', hi'⟩, ?_, ?_, ?_⟩
  · simp [w', AffineMap.lineMap_apply_module, Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]
  · simp [w', hri']
  · intro i
    obtain ⟨r, hr⟩ := hp'' i
    refine ⟨r, ?_⟩
    rw [← hri'] at hr
    simp only [AffineMap.lineMap_apply_module] at hr
    have hind := hp.indicator_eq_of_affineCombination_eq _ _ _ _ ?_ ?_ hr
    · intro j
      by_cases hj : j = i
      · simp [hj]
      replace hind := congr_fun hind j
      convert hind using 1
      · simp [Set.indicator_apply, hj]
      · simp [Set.indicator_apply, hj, w', AffineMap.lineMap_apply_module]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]


theorem exists_affineCombination_eq_smul_eq {p : ι → P} (hp : AffineIndependent k p) {s : Set ι}
    (hs : s.Nonempty) {fs : s → Finset ι} {w : s → ι → k} (hw : ∀ i, ∑ j ∈ fs i, w i j = 1) {p' : P}
    (hp' : ∀ i : s, p' ∈ line[k, p i, (fs i).affineCombination k p (w i)]) :
    ∃ (w' : ι → k) (fs' : Finset ι), (∑ j ∈ fs', w' j = 1) ∧ fs'.affineCombination k p w' = p' ∧
      ∀ i : s, ∃ r, ∀ j, r * Set.indicator ((fs i : Set ι) \ {(i : ι)}) (w i) j =
        Set.indicator ((fs' : Set ι) \ {(i : ι)}) w' j := by
  classical
  let fsx : s → Finset ι := fun i ↦ insert (i : ι) (fs i)
  have hfsx : ∀ i, (i : ι) ∈ fsx i := by simp [fsx]
  let wx : s → ι → k := fun i ↦ Set.indicator (fs i) (w i)
  have hwx : ∀ i, ∑ j ∈ fsx i, wx i j = 1 := by
    intro i
    simp_rw [← hw i, fsx, wx]
    by_cases hi : (i : ι) ∈ fs i <;> simpa [hi] using Finset.sum_congr rfl (by aesop)
  have hp'x : ∀ i : s, p' ∈ line[k, p i, (fsx i).affineCombination k p (wx i)] := by
    intro i
    convert hp' i using 4
    simp_rw [fsx, wx]
    exact (Finset.affineCombination_indicator_subset _ _ (by simp)).symm
  obtain ⟨w', fs', h⟩ := exists_affineCombination_eq_smul_eq_aux hp hs hfsx hwx hp'x
  refine ⟨w', fs', h.1, h.2.1, fun i ↦ ?_⟩
  obtain ⟨r, hr⟩ := h.2.2 i
  refine ⟨r, fun j ↦ ?_⟩
  convert hr j using 2
  simp only [Set.indicator_apply, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff,
    Finset.coe_insert, Set.insert_diff_of_mem, fsx, wx]
  grind

