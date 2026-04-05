import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem kernelSequenceE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceOpcyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements
      (X.liftOpcycles f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        dsimp
        rw [← X.fromOpcyles_δ f₁ f₂ f₃ f₂₃ h₂₃ n₁ n₂,
          X.liftOpcycles_fromOpcycles_assoc]
        simpa using hx₂ =≫ biprod.snd)
  dsimp at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁, ?_⟩
  dsimp
  rw [← reassoc_of% hx₁, liftOpcycles_fromOpcycles]

