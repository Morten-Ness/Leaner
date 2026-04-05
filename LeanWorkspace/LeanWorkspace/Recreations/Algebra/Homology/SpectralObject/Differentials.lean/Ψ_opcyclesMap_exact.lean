import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem Ψ_opcyclesMap_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (X.Ψ_opcyclesMap f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro _ z₀ hz₀
  obtain ⟨A₁, π₁, _, z₁, hz₁⟩ := surjective_up_to_refinements_of_epi (X.pOpcycles f₁ f₂ n₁) z₀
  obtain ⟨A₂, π₂, _, z₂, hz₂⟩ :=
      (X.cokernelSequenceOpcycles_exact f₁ f₂₃ n₀ n₁ hn₁).exact_up_to_refinements z₁ (by
    dsimp
    have H := X.p_opcyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) (𝟙 _) n₁ (by cat_disch)
    rw [Functor.map_id, id_comp] at H
    rw [← H, ← reassoc_of% hz₁, hz₀, comp_zero])
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z₂ ≫ X.toCycles f₂ f₃ f₂₃ h₂₃ n₀, ?_⟩
  rw [← cancel_mono (X.fromOpcycles f₁ f₂ f₁₂ h₁₂ n₁), assoc, assoc,
    assoc, assoc, toCycles_Ψ_assoc .., p_fromOpcycles, ← reassoc_of% dsimp% hz₂,
    reassoc_of% hz₁, p_fromOpcycles]

