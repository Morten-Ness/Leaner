import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]

variable (D : SnakeInput C)

theorem δ_apply' (x₃ : (forget₂ C Ab).obj D.L₀.X₃)
    (x₂ : (forget₂ C Ab).obj D.L₁.X₂) (x₁ : (forget₂ C Ab).obj D.L₂.X₁)
    (h₂ : (forget₂ C Ab).map D.L₁.g x₂ = (forget₂ C Ab).map D.v₀₁.τ₃ x₃)
    (h₁ : (forget₂ C Ab).map D.L₂.f x₁ = (forget₂ C Ab).map D.v₁₂.τ₂ x₂) :
    (forget₂ C Ab).map D.δ x₃ = (forget₂ C Ab).map D.v₂₃.τ₁ x₁ := by
  have e : forget₂ C Ab ⋙ forget Ab ≅ forget C := eqToIso (HasForget₂.forget_comp)
  apply (mono_iff_injective (e.hom.app _)).1 inferInstance
  exact (ConcreteCategory.congr_hom (e.hom.naturality D.δ) x₃).trans ((D.δ_apply _ _ _
    (((congr_fun (e.hom.naturality D.L₁.g) x₂).symm.trans (by simp [h₂])).trans
      (congr_fun (e.hom.naturality D.v₀₁.τ₃) x₃))
    (((congr_fun (e.hom.naturality D.L₂.f) x₁).symm.trans (by simp [h₁])).trans
      (congr_fun (e.hom.naturality D.v₁₂.τ₂) x₂))).trans
    (ConcreteCategory.congr_hom (e.hom.naturality D.v₂₃.τ₁).symm x₁))

