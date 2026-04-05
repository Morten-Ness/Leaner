import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ f₂₃))
  (h : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃) = 0)
  (hn₂ : n₁ + 1 = n₂)
  (h' : x ≫ X.δ f₁ f₂₃ n₁ n₂ hn₂ = 0)

theorem liftE_ιE_fromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.liftE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ x h hn₂ h' hn₁ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ = x := by
  apply (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).lift_f

