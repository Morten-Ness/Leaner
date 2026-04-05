import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {s : Finset ι} {w w₁ w₂ : ι → k} {p : ι → V}

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


theorem affineCombination_mem_affineSpan_pair {p : ι → P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι → k} {s : Finset ι} (_ : ∑ i ∈ s, w i = 1) (hw₁ : ∑ i ∈ s, w₁ i = 1)
    (hw₂ : ∑ i ∈ s, w₂ i = 1) :
    s.affineCombination k p w ∈ line[k, s.affineCombination k p w₁, s.affineCombination k p w₂] ↔
      ∃ r : k, ∀ i ∈ s, w i = r * (w₂ i - w₁ i) + w₁ i := by
  rw [← vsub_vadd (s.affineCombination k p w) (s.affineCombination k p w₁),
    AffineSubspace.vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _),
    direction_affineSpan, s.affineCombination_vsub, Set.pair_comm,
    weightedVSub_mem_vectorSpan_pair h _ hw₂ hw₁]
  · simp only [Pi.sub_apply, sub_eq_iff_eq_add]
  · simp_all only [Pi.sub_apply, Finset.sum_sub_distrib, sub_self]

