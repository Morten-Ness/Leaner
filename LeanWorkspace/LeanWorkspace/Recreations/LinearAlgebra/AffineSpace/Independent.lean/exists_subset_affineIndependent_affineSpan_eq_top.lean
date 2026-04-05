import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

private theorem AffineIndependent.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton
    [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p) {s₁ s₂ : Set ι} {i : ι}
    (his₁ : i ∈ s₁) (his₂ : i ∉ s₂) (h₁ : ¬s₁.Subsingleton) :
    vectorSpan k (p '' s₁) ≠ vectorSpan k (p '' s₂) := by
  classical
  rw [Set.not_subsingleton_iff] at h₁
  obtain ⟨j, hj, hne⟩ := h₁.exists_ne i
  intro he
  have hs : p i -ᵥ p j ∈ vectorSpan k (p '' s₁) :=
    vsub_mem_vectorSpan k (Set.mem_image_of_mem _ his₁) (Set.mem_image_of_mem _ hj)
  rw [he, Set.image_eq_range, mem_vectorSpan_iff_eq_weightedVSub] at hs
  obtain ⟨fs, w, hw, hs⟩ := hs
  let w' : ι → k := Function.extend Subtype.val w 0
  have hw' : ∑ t ∈ fs.map (Embedding.subtype _), w' t = 0 := by
    simp only [sum_map, Embedding.subtype_apply, ← hw]
    exact sum_congr rfl fun t ht ↦ by simp [w']
  have hs' : p i -ᵥ p j = (fs.map (Embedding.subtype _)).weightedVSub p w' := by
    rw [hs, weightedVSub_map]
    simp [w', Function.comp_def]
  let fs' : Finset ι := insert i (insert j (fs.map (Embedding.subtype _)))
  have hfsfs' : fs.map (Embedding.subtype _) ⊆ fs' := by grind
  let w'' : ι → k := Set.indicator (fs.map (Embedding.subtype _)) w'
  have hs'' : p i -ᵥ p j = fs'.weightedVSub p w'' := by
    rw [hs']
    exact weightedVSubOfPoint_indicator_subset _ _ _ (by grind)
  have hw'' : ∑ t ∈ fs', w'' t = 0 := by
    rw [← hw']
    exact sum_indicator_subset _ (by grind)
  let w''' : ι → k := w'' - weightedVSubVSubWeights k i j
  have hi : i ∈ fs' := by grind
  have hj : j ∈ fs' := by grind
  have hw''' : ∑ t ∈ fs', w''' t = 0 := by
    simp [w''', sum_sub_distrib, hw'', hi, hj]
  have hs''' : fs'.weightedVSub p w''' = 0 := by
    simp [w''', ← hs'', hi, hj]
  have h0 := ha fs' w''' hw''' hs''' i hi
  simp [w''', w'', Pi.sub_apply, hne.symm, his₂] at h0


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

