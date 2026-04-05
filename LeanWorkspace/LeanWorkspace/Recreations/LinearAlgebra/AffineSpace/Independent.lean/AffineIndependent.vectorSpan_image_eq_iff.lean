import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

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


theorem AffineIndependent.vectorSpan_image_eq_iff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s₁ s₂ : Set ι} :
    vectorSpan k (p '' s₁) = vectorSpan k (p '' s₂) ↔
      s₁ = s₂ ∨ s₁.Subsingleton ∧ s₂.Subsingleton := by
  constructor
  · intro h
    by_cases he : s₁ = s₂
    · simp [he]
    simp only [he, false_or]
    by_cases h₁ : s₁.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₁.image _), eq_comm, vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨h₁, Set.subsingleton_of_image ha.injective s₂ h⟩
    by_cases h₂ : s₂.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₂.image _), vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨Set.subsingleton_of_image ha.injective s₁ h, h₂⟩
    simp only [h₁, h₂, false_and]
    have hi : (∃ i ∈ s₁, i ∉ s₂) ∨ ∃ i ∈ s₂, i ∉ s₁ := by grind
    rcases hi with ⟨i, his₁, his₂⟩ | ⟨i, his₂, his₁⟩
    · exact ha.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton his₁ his₂ h₁ h
    · exact ha.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton his₂ his₁ h₂ h.symm
  · intro h
    rcases h with rfl | ⟨h₁, h₂⟩
    · rfl
    · simp [h₁.image p, h₂.image p, vectorSpan_of_subsingleton]

