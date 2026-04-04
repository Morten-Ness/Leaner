import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

theorem affineCombination_mem_affineSpan_image [Nontrivial k] {s : Finset ι} {w : ι → k}
    (h : ∑ i ∈ s, w i = 1) {s' : Set ι} (hs' : ∀ i ∈ s, i ∉ s' → w i = 0) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (p '' s') := by
  classical
  rw [Set.image_eq_range]
  let w' : s' → k := fun i ↦ w i
  have h' : ∑ i ∈ s with i ∈ s', w i = 1 := by
    rw [← h, ← Finset.sum_sdiff (s₁ := {x ∈ s | x ∈ s'}) (s₂ := s) (by simp), right_eq_add]
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_filter, not_and] at hi
    exact hs' i hi.1 (hi.2 hi.1)
  rw [← Finset.sum_subtype_eq_sum_filter] at h'
  convert affineCombination_mem_affineSpan h' (fun x ↦ p x)
  rw [Finset.affineCombination_subtype_eq_filter, Finset.affineCombination_indicator_subset w p
    (Finset.filter_subset _ _)]
  refine Finset.affineCombination_congr _ (fun i hi ↦ ?_) (fun _ _ ↦ rfl)
  simp_all [Set.indicator_apply]

