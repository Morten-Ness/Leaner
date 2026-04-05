import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem δToCycles_cyclesIso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).toCycles := by
  simp [← cancel_mono (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).iCycles]

