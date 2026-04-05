import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

theorem comp_assoc_of_second_deg_zero
    {a₁ a₃ a₁₃ : ℕ} (α : CategoryTheory.Abelian.Ext X Y a₁) (β : CategoryTheory.Abelian.Ext Y Z 0) (γ : CategoryTheory.Abelian.Ext Z T a₃)
    (h₁₃ : a₁ + a₃ = a₁₃) :
    (α.comp β (add_zero _)).comp γ h₁₃ = α.comp (β.comp γ (zero_add _)) h₁₃ := by
  apply CategoryTheory.Abelian.Ext.comp_assoc
  lia

