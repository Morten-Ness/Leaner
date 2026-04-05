import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

theorem comp_assoc_of_third_deg_zero
    {a₁ a₂ a₁₂ : ℕ} (α : CategoryTheory.Abelian.Ext X Y a₁) (β : CategoryTheory.Abelian.Ext Y Z a₂) (γ : CategoryTheory.Abelian.Ext Z T 0)
    (h₁₂ : a₁ + a₂ = a₁₂) :
    (α.comp β h₁₂).comp γ (add_zero _) = α.comp (β.comp γ (add_zero _)) h₁₂ := by
  apply CategoryTheory.Abelian.Ext.comp_assoc
  lia

