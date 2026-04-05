import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

theorem comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : ℕ} (α : CategoryTheory.Abelian.Ext X Y a₁) (β : CategoryTheory.Abelian.Ext Y Z a₂) (γ : CategoryTheory.Abelian.Ext Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show a₁₂ + a₃ = a by lia) =
      α.comp (β.comp γ h₂₃) (by lia) := SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by lia)

