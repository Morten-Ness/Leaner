import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] [Category* ι]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem dCokernelSequence_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    (X.dCokernelSequence f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄ n₀ n₁ n₂ n₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at hx₂ ⊢
  have hx₂' := hx₂ =≫ X.ιE ..
  rw [assoc, zero_comp, X.map_ιE f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄)
    (threeδ₃Toδ₂ f₂ f₃ f₄ f₃₄) n₁ n₂ n₃] at hx₂'
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    ((X.sequenceΨ_exact f₂ f₃ f₄ _ rfl f₃₄ h₃₄ n₁ n₂).exact 1).exact_up_to_refinements
      (x₂ ≫ X.ιE ..) (by simp [sequenceΨ, Precomp.map, hx₂'])
  dsimp [sequenceΨ, Precomp.map] at hx₁
  refine ⟨A₁, π₁, inferInstance, x₁ ≫ X.πE f₃ f₄ f₅ n₀ n₁ n₂, ?_⟩
  rw [← cancel_mono (X.ιE ..), assoc, assoc, assoc, hx₁, πE_d_ιE ..]

