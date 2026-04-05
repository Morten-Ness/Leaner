import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

theorem cokernelSequenceE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceCyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁) (by simpa using hx₂)
  dsimp at y₁ hy₁
  let z := π₁ ≫ x₂ - y₁ ≫ X.δ f₁₂ f₃ n₀ n₁
  obtain ⟨A₂, π₂, _, x₁, hx₁⟩ := (X.exact₂ f₁ f₂ f₁₂ h₁₂ n₁).exact_up_to_refinements z (by
      have : z ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ = 0 := by simp [z, hy₁]
      simpa only [zero_comp, Category.assoc, toCycles_i] using this =≫ X.iCycles f₁ f₂ n₁)
  dsimp at x₁ hx₁
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, biprod.lift x₁ (π₂ ≫ y₁), by simp [z, ← hx₁]⟩

