import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
  (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem kernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceCyclesE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.iCycles f₁ f₂₃ n₁) (by cat_disch)
  exact ⟨A₁, π₁, inferInstance, x₁, by simpa [← cancel_mono (X.iCycles ..)]⟩

