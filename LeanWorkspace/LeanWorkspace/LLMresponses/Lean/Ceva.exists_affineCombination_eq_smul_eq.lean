FAIL
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
  by_cases hfs : ∀ i : s, (i : ι) ∈ fs i
  · exact exists_affineCombination_eq_smul_eq_aux hp hs hfs hw hp'
  · have hnot : ∃ i : s, (i : ι) ∉ fs i := by
      simpa only [not_forall] using hfs
    obtain ⟨i, hi⟩ := hnot
    exact exists_affineCombination_eq_smul_eq_aux hp hs
      (fun j =>
        by
          by_cases hj : (j : ι) ∈ fs j
          · exact hj
          · exfalso
            exact hi hj)
      hw hp'
