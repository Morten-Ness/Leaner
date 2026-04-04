import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem affineCombination_mem_affineSpan_faceOpposite_iff {n : ℕ} [NeZero n] {s : Affine.Simplex k P n}
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) {i : Fin (n + 1)} :
    Finset.univ.affineCombination k s.points w ∈
      affineSpan k (Set.range (s.faceOpposite i).points) ↔ w i = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [range_faceOpposite_points] at h
    exact s.independent.eq_zero_of_affineCombination_mem_affineSpan hw h (Finset.mem_univ i)
      (by simp)
  · rw [range_faceOpposite_points]
    rcases subsingleton_or_nontrivial k with hk | hk
    · have : Subsingleton V := Module.subsingleton k _
      have : Subsingleton P := (AddTorsor.subsingleton_iff V P).1 inferInstance
      rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (by simp)]
      simp
    · exact affineCombination_mem_affineSpan_image hw (by simpa using h) s.points

