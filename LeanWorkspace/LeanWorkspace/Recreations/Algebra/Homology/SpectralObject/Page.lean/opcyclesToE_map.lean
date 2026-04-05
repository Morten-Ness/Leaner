import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  {i₀' i₁' i₂' i₃' : ι} (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (f₁₂' : i₀' ⟶ i₂') (h₁₂' : f₁' ≫ f₂' = f₁₂')

set_option backward.isDefEq.respectTransparency false in
theorem opcyclesToE_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (β : mk₂ f₁₂ f₃ ⟶ mk₂ f₁₂' f₃')
    (n₀ n₁ n₂ : ℤ) (h₀ : β.app 0 = α.app 0 := by cat_disch) (h₁ : β.app 1 = α.app 2 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ X.map _ _ _ _ _ _ α _ _ _ =
      X.opcyclesMap _ _ _ _ β _ ≫ X.opcyclesToE f₁' f₂' f₃' f₁₂' h₁₂' n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← cancel_mono (X.ιE ..), Category.assoc, Category.assoc, CategoryTheory.Abelian.SpectralObject.opcyclesToE_ιE ..,
    ← cancel_epi (X.pOpcycles ..), p_opcyclesToE_assoc ..,
    X.πE_map_assoc _ _ _ _ _ _ _
      (homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1) (naturality' α 1 2)) ..,
    CategoryTheory.Abelian.SpectralObject.πE_ιE .., X.cyclesMap_i_assoc .., toCycles_i_assoc,
    X.p_opcyclesMap_assoc .., X.p_opcyclesMap ..,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  ext
  · simpa [h₀] using naturality' α 0 1
  · simp [h₁]

