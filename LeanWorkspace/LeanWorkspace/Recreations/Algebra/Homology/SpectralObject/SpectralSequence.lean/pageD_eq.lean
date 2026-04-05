import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

set_option backward.isDefEq.respectTransparency false in
theorem pageD_eq (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq')
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD X data r pq pq' =
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso _ _ _ _ _ _ _ _ _ h₂ h₃ h₄ h₅ _ _ _ hn₁' _ _).hom ≫
        X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
        (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso _ _ _ _ _ _ _ _ _ h₀ h₁ (by rw [h₂, data.hc₀₂ r pq pq' hpq])
          (by rw [h₃, data.hc₁₃ r pq pq' hpq]) _ _ _
          (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq) _ _).inv := by
  subst hn₁' h₀ h₁ h₂ h₃ h₄ h₅
  obtain rfl : n₀ = data.deg pq - 1 := by lia
  obtain rfl : n₂ = data.deg pq + 1 := by lia
  obtain rfl : n₃ = data.deg pq + 2 := by lia
  dsimp [CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD, CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso]
  rw [dif_pos hpq, Category.id_comp]
  rfl

