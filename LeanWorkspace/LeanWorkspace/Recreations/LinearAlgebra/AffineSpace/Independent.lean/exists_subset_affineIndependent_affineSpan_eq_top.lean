import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem exists_subset_affineIndependent_affineSpan_eq_top {s : Set P}
    (h : AffineIndependent k (fun p => p : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ AffineIndependent k (fun p => p : t → P) ∧ affineSpan k t = ⊤ := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p₁, hp₁⟩)
  · have p₁ : P := AddTorsor.nonempty.some
    let hsv := Basis.ofVectorSpace k V
    have hsvi := hsv.linearIndependent
    have hsvt := hsv.span_eq
    rw [Basis.coe_ofVectorSpace] at hsvi hsvt
    have h0 : ∀ v : V, v ∈ Basis.ofVectorSpaceIndex k V → v ≠ 0 := by
      intro v hv
      simpa [hsv] using hsv.ne_zero ⟨v, hv⟩
    rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi
    exact
      ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' _, Set.empty_subset _, hsvi,
        affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩
  · rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁] at h
    let bsv := Basis.extend h
    have hsvi := bsv.linearIndependent
    have hsvt := bsv.span_eq
    rw [Basis.coe_extend] at hsvi hsvt
    rw [linearIndependent_subtype_iff] at hsvi h
    have hsv := h.subset_extend (Set.subset_univ _)
    have h0 : ∀ v : V, v ∈ h.extend (Set.subset_univ _) → v ≠ 0 := by
      intro v hv
      simpa [bsv] using bsv.ne_zero ⟨v, hv⟩
    rw [← linearIndependent_subtype_iff,
      linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi
    refine ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' h.extend (Set.subset_univ _), ?_, ?_⟩
    · refine Set.Subset.trans ?_ (Set.union_subset_union_right _ (Set.image_mono hsv))
      simp [Set.image_image]
    · use hsvi
      exact affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt

