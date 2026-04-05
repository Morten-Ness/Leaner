import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] [Category* ι]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem dKernelSequence_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    (X.dKernelSequence f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₀ n₁ n₂ n₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at hx₂ ⊢
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂) x₂
  have hy₂' := hy₂ =≫ X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ ≫ X.ιE ..
  simp only [assoc, reassoc_of% hx₂, zero_comp, comp_zero, πE_d_ιE] at hy₂'
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    ((X.sequenceΨ_exact f₂ f₃ f₄ f₂₃ h₂₃ _ rfl n₁ n₂).exact 0).exact_up_to_refinements y₂ hy₂'.symm
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y₁ ≫ X.πE f₂₃ f₄ f₅ n₀ n₁ n₂, ?_⟩
  simp [sequenceΨ, hy₂, reassoc_of% hy₁, X.πE_map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃)
    (threeδ₁Toδ₀ f₂ f₃ f₄ f₂₃) n₀ n₁ n₂]

