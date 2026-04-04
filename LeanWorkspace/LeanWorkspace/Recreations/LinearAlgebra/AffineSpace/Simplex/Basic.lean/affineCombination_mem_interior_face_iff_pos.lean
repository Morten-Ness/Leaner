import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem affineCombination_mem_interior_face_iff_pos [IsOrderedAddMonoid k] {n : ℕ}
    (s : Affine.Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} [NeZero m] (h : #fs = m + 1)
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ (s.face h).interior ↔
      (∀ i ∈ fs, 0 < w i) ∧ (∀ i ∉ fs, w i = 0) := by
  rw [s.affineCombination_mem_interior_face_iff_mem_Ioo h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ ↦ ⟨fun i hi ↦ ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw, ← Finset.sum_subset (Finset.subset_univ fs) fun j _ ↦ hi0 j]
  obtain ⟨j, hj, hji⟩ := fs.exists_mem_ne (by grind [→ NeZero.ne]) i
  exact Finset.single_lt_sum hji hi hj (hii j hj) fun t ht _ ↦ (hii t ht).le

