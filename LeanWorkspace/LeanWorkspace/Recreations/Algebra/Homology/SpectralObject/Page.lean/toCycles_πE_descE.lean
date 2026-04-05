import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

variable {A : C} (x : (X.H n₁).obj (mk₁ f₁₂) ⟶ A)
  (h : (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ x = 0)
  (hn₁ : n₀ + 1 = n₁) (h' : X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ x = 0)

theorem toCycles_πE_descE (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.descE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ x h hn₁ h' hn₂ = x := by
  dsimp only [CategoryTheory.Abelian.SpectralObject.descE]
  rw [← Category.assoc]
  apply (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).g_desc

