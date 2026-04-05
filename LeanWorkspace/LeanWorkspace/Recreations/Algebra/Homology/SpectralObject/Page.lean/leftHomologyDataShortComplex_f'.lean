import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem leftHomologyDataShortComplex_f' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).f' =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  exact Fork.IsLimit.hom_ext hi (by simpa using hi.fac _ .zero)

