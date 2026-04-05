import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable (k V)

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


theorem exists_affineIndependent (s : Set P) :
    ∃ t ⊆ s, affineSpan k t = affineSpan k s ∧ AffineIndependent k ((↑) : t → P) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · exact ⟨∅, Set.empty_subset ∅, rfl, affineIndependent_of_subsingleton k _⟩
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linearIndependent k ((Equiv.vaddConst p).symm '' s)
  have hb₀ : ∀ v : V, v ∈ b → v ≠ 0 := fun v hv => hb₃.ne_zero (⟨v, hv⟩ : b)
  rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k hb₀ p] at hb₃
  refine ⟨{p} ∪ Equiv.vaddConst p '' b, ?_, ?_, hb₃⟩
  · apply Set.union_subset (Set.singleton_subset_iff.mpr hp)
    rwa [← (Equiv.vaddConst p).subset_symm_image b s]
  · rw [Equiv.coe_vaddConst_symm, ← vectorSpan_eq_span_vsub_set_right k hp] at hb₂
    apply AffineSubspace.ext_of_direction_eq
    · have : Submodule.span k b = Submodule.span k (insert 0 b) := by simp
      simp only [direction_affineSpan, ← hb₂, Equiv.coe_vaddConst, Set.singleton_union,
        vectorSpan_eq_span_vsub_set_right k (Set.mem_insert p _), this]
      congr
      change (Equiv.vaddConst p).symm '' insert p (Equiv.vaddConst p '' b) = _
      rw [Set.image_insert_eq, ← Set.image_comp]
      simp
    · use p
      simp only [Equiv.coe_vaddConst, Set.singleton_union, Set.mem_inter_iff]
      exact ⟨mem_affineSpan k (Set.mem_insert p _), mem_affineSpan k hp⟩

