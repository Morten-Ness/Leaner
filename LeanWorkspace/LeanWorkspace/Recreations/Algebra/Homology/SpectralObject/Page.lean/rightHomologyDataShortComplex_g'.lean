import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem rightHomologyDataShortComplex_g'
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g' =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  exact Cofork.IsColimit.hom_ext hp (by simpa using hp.fac _ .one)

