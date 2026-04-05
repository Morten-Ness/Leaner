import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)

theorem Ψ_fromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.fromOpcycles f₁ f₂ f₁₂ h₁₂ n₁ =
      X.iCycles f₂ f₃ n₀ ≫ X.δ f₁₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_epi (X.toCycles f₂ f₃ _ rfl n₀),
    toCycles_Ψ_assoc .., p_fromOpcycles, toCycles_i_assoc]
  exact (X.δ_naturality _ _ _ _ _ _ _ _ rfl).symm

