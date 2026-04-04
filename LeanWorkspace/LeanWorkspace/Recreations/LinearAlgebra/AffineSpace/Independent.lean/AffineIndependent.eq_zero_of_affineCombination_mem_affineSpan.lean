import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι → P}
    (ha : AffineIndependent k p) {fs : Finset ι} {w : ι → k} (hw : ∑ i ∈ fs, w i = 1) {s : Set ι}
    (hm : fs.affineCombination k p w ∈ affineSpan k (p '' s)) {i : ι} (hifs : i ∈ fs)
    (his : i ∉ s) : w i = 0 := by
  obtain ⟨fs', w', hfs's, hw', he⟩ := eq_affineCombination_of_mem_affineSpan_image hm
  have hi' : (fs : Set ι).indicator w i = 0 := by
    rw [ha.indicator_eq_of_affineCombination_eq fs fs' w w' hw hw' he]
    exact Set.indicator_of_notMem (Set.notMem_subset hfs's his) w'
  rw [Set.indicator_apply_eq_zero] at hi'
  exact hi' (Finset.mem_coe.2 hifs)

