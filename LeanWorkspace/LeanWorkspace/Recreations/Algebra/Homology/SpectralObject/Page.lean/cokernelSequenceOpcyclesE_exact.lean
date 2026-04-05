import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
  (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem cokernelSequenceOpcyclesE_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles f₁₂ f₃ n₁) x₂
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements y₂
      (by simpa only [Category.assoc, CategoryTheory.Abelian.SpectralObject.p_opcyclesToE, hx₂, comp_zero]
        using hy₂.symm =≫ X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)
  dsimp at y₁ hy₁
  obtain ⟨a, b, rfl⟩ : ∃ a b, y₁ = a ≫ biprod.inl + b ≫ biprod.inr :=
    ⟨y₁ ≫ biprod.fst, y₁ ≫ biprod.snd, by ext <;> simp⟩
  simp only [Preadditive.add_comp, Category.assoc, biprod.inl_desc, biprod.inr_desc] at hy₁
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, a, ?_⟩
  simp [Category.assoc, hy₂, reassoc_of% hy₁, Preadditive.add_comp, δ_pOpcycles,
    comp_zero, add_zero]

-- TODO: add dual statement to `cokernelSequenceOpcyclesE_exact`?

