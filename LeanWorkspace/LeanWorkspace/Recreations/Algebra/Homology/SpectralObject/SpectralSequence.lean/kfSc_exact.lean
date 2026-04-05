import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq')
  (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq')
  (hi₃' : i₃' = data.i₃ r' pq')
  (n₀ n₁ n₂ : ℤ)
  (hn₁' : n₁ = data.deg pq')

include hpq' in
theorem kfSc_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.kfSc X data r r' hrr' hr pq' pq'' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃
      n₀ n₁ n₂ hn₁' hn₁ hn₂).Exact := by
  by_cases h : (c r).Rel pq' pq''
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dKernelSequence_exact
        (homOfLE (show data.i₀ r pq'' ≤ i₀' by
          simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
        (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
        (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) _ rfl
        n₀ n₁ n₂ (n₂ + 1) hn₁ hn₂ rfl)
    refine ShortComplex.isoMk (Iso.refl _)
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁')
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso X data _ hr _ _ _ _ _ rfl (by rw [hi₀', data.i₀_prev r r' _ _ h])
      (by rw [hi₀, data.hc₀₂ r _ _ h]) (by rw [hi₁, data.hc₁₃ r _ _ h]) _ _ _
      (by have := data.hc r _ _ h; lia)) ?_ ?_
    · simp
    · dsimp
      rw [CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq X data r hr pq' pq'' h
        (homOfLE (data.le₀₁' r hr pq'' rfl (by simpa [← data.i₀_prev r r' _ _ h])))
        (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
        (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
        rfl (by rw [hi₀', data.i₀_prev r r' _ _ h]) hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ (n₂ + 1) hn₁',
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [ShortComplex.exact_iff_epi _ ((CategoryTheory.Abelian.SpectralObject.SpectralSequence.page X data r hr).shape _ _ h)]
    have := CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isIso_mapFourδ₁Toδ₀' X data r r' hrr' hr pq' pq'' hpq'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' h
    dsimp
    infer_instance

