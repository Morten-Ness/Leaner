import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

theorem cyclesIso_hom_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.iCycles f₁ f₂ n₁ =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles :=
  ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

