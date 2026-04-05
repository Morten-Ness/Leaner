import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

theorem pageD_pageD (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ) :
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD X data r pq pq' hr ≫ CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD X data r pq' pq'' hr = 0 := by
  by_cases hpq : (c r).Rel pq pq'
  · by_cases hpq' : (c r).Rel pq' pq''
    · rw [CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq X data r hr pq pq' hpq (homOfLE (data.le₂₃ r pq''))
          (homOfLE (data.le₁₂' pq' (data.hc₁₃ r pq' pq'' hpq').symm
          (data.hc₀₂ r pq pq' hpq))) (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
          (homOfLE (data.le₂₃ r pq))
          (data.hc₀₂ r pq' pq'' hpq').symm (data.hc₁₃ r pq' pq'' hpq').symm rfl rfl rfl rfl
          (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) rfl,
        CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq X data r hr pq' pq'' hpq' (homOfLE (data.le₀₁ r pq''))
          (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq''))
          (homOfLE (data.le₁₂' pq' (data.hc₁₃ r pq' pq'' hpq').symm (data.hc₀₂ r pq pq' hpq)))
          (homOfLE (data.le₀₁ r pq)) rfl rfl
          (data.hc₀₂ r pq' pq'' hpq').symm (data.hc₁₃ r pq' pq'' hpq').symm
          (data.hc₀₂ r pq pq' hpq) (data.hc₁₃ r pq pq' hpq)
          _ _ (data.deg pq + 2) _ (data.hc r pq pq' hpq) rfl (by lia) rfl,
        Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
        d_d_assoc .., zero_comp, comp_zero]
    · dsimp only [CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD]
      rw [dif_neg hpq', comp_zero]
  · dsimp only [CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD]
    rw [dif_neg hpq, zero_comp]

