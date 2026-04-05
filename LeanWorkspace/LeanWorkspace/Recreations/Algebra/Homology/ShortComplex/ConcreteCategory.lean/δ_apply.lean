import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]

variable (D : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem δ_apply (x₃ : ToType (D.L₀.X₃)) (x₂ : ToType (D.L₁.X₂)) (x₁ : ToType (D.L₂.X₁))
    (h₂ : D.L₁.g x₂ = D.v₀₁.τ₃ x₃) (h₁ : D.L₂.f x₁ = D.v₁₂.τ₂ x₂) :
    D.δ x₃ = D.v₂₃.τ₁ x₁ := by
  have := (forget₂ C Ab).preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteLimits (forget C) := by
    have : forget₂ C Ab ⋙ forget Ab = forget C := HasForget₂.forget_comp
    simpa only [← this] using comp_preservesFiniteLimits _ _
  have eq := CategoryTheory.congr_fun (D.snd_δ)
    (Limits.Concrete.pullbackMk D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂)
  have eq₁ := Concrete.pullbackMk_fst D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  have eq₂ := Concrete.pullbackMk_snd D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at eq
  rw [eq₂] at eq
  refine eq.trans (CategoryTheory.congr_arg (D.v₂₃.τ₁) ?_)
  apply (CategoryTheory.Preadditive.mono_iff_injective' D.L₂.f).1 inferInstance
  rw [← ConcreteCategory.comp_apply, φ₁_L₂_f]
  dsimp [φ₂]
  rw [ConcreteCategory.comp_apply, eq₁]
  exact h₁.symm

