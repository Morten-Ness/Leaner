import Mathlib

variable {k V P ι : Type*}

variable [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

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
  obtain ⟨w', fs', h⟩ := hp.exists_affineCombination_eq_smul_eq_aux hs hfsx hwx hp'x
  refine ⟨w', fs', h.1, h.2.1, fun i ↦ ?_⟩
  obtain ⟨r, hr⟩ := h.2.2 i
  refine ⟨r, fun j ↦ ?_⟩
  convert hr j using 2
  simp only [Set.indicator_apply, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff,
    Finset.coe_insert, Set.insert_diff_of_mem, fsx, wx]
  grind

