import Mathlib

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem associator_inv_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).inv.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).inv :=
  rfl

