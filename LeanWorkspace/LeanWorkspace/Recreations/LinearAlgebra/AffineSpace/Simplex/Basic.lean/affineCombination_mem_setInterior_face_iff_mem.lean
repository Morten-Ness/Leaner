import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem affineCombination_mem_setInterior_face_iff_mem (I : Set k) {n : ℕ} (s : Affine.Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w ∈ (s.face h).setInterior I ↔
      (∀ i ∈ fs, w i ∈ I) ∧ (∀ i ∉ fs, w i = 0) := by
  refine ⟨fun hi ↦ ?_, fun ⟨hii, hi0⟩ ↦ ?_⟩
  · obtain ⟨w', hw', he⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      (Set.mem_of_mem_of_subset hi Affine.Simplex.setInterior_subset_affineSpan)
    rw [he, Affine.Simplex.affineCombination_mem_setInterior_iff hw'] at hi
    have he' := s.independent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
      hw hw' (fs.orderEmbOfFin h).toEmbedding he.symm
    simp_rw [he'.symm]
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ by simp [hi]⟩
    simp only [RelEmbedding.coe_toEmbedding, range_orderEmbOfFin, mem_coe, hi, Set.indicator_of_mem]
    rw [← mem_coe, ← fs.range_orderEmbOfFin h] at hi
    obtain ⟨j, rfl⟩ := hi
    simp [(fs.orderEmbOfFin h).injective.extend_apply, hi]
  · let w' : Fin (m + 1) → k := w ∘ fs.orderEmbOfFin h
    have hw' : ∑ i, w' i = 1 := by
      rw [Fintype.sum_of_injective _ (fs.orderEmbOfFin h).injective w' w
        (fun i hi ↦ hi0 _ (by simpa using hi)) (fun _ ↦ rfl), hw]
    have hw'01 (i) : w' i ∈ I := hii (fs.orderEmbOfFin h i) (by simp)
    rw [← (s.face h).affineCombination_mem_setInterior_iff hw'] at hw'01
    convert hw'01
    convert Finset.univ.affineCombination_map (fs.orderEmbOfFin h).toEmbedding w s.points using 1
    simp only [map_orderEmbOfFin_univ, Finset.affineCombination_indicator_subset _ _ fs.subset_univ]
    congr
    grind [Set.indicator_eq_self, support_subset_iff]

