import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

theorem cyclesMap_Ψ_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (X.cyclesMap_Ψ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A z hz
  refine ⟨A, 𝟙 _, inferInstance,
    X.liftCycles f₁₂ f₃ n₀ n₁ hn₁ (z ≫ X.iCycles f₂ f₃ n₀) ?_, ?_⟩ <;> dsimp
  · rw [assoc, ← X.Ψ_fromOpcycles f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ hn₁, reassoc_of% hz, zero_comp]
  · rw [← cancel_mono (X.iCycles f₂ f₃ n₀), id_comp, assoc,
      X.cyclesMap_i _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) (𝟙 _) n₀ (by cat_disch) ,
      Functor.map_id, comp_id, liftCycles_i]

