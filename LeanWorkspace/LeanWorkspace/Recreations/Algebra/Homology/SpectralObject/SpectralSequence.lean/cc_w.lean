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

theorem cc_w (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (CategoryTheory.Abelian.SpectralObject.SpectralSequence.page X data r hr).d pq pq' ≫
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁').hom ≫
      X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' _ _ _
        (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ = 0 := by
  by_cases h : (c r).Rel pq pq'
  · dsimp
    rw [CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq X data r hr pq pq' h (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
      (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
      (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
      (homOfLE (by simpa only [hi₃', data.i₃_next r r' _ _ h] using data.le₂₃ r pq))
      hi₀ hi₁ (by rw [hi₂, data.hc₀₂ r _ _ h])
      (by rw [hi₃, data.hc₁₃ r _ _ h]) (by rw [hi₃', data.i₃_next r r' _ _ h]) rfl
      (n₀ - 1) n₀ n₁ n₂ (by have := data.hc r pq pq' h; lia) (by simp) hn₁ hn₂,
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      d_map_fourδ₄Toδ₃ .., comp_zero]
    rfl
  · rw [HomologicalComplex.shape _ _ _ h, zero_comp]

