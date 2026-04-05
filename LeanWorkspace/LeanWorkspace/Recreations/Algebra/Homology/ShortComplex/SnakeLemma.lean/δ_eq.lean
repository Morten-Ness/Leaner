import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem δ_eq {A : C} (x₃ : A ⟶ S.L₀.X₃) (x₂ : A ⟶ S.L₁.X₂) (x₁ : A ⟶ S.L₂.X₁)
    (h₂ : x₂ ≫ S.L₁.g = x₃ ≫ S.v₀₁.τ₃) (h₁ : x₁ ≫ S.L₂.f = x₂ ≫ S.v₁₂.τ₂) :
    x₃ ≫ S.δ = x₁ ≫ S.v₂₃.τ₁ := by
  have H := (pullback.lift x₂ x₃ h₂) ≫= S.snd_δ
  rw [pullback.lift_snd_assoc] at H
  rw [H, ← assoc]
  congr 1
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, CategoryTheory.ShortComplex.SnakeInput.lift_φ₂, h₁]

