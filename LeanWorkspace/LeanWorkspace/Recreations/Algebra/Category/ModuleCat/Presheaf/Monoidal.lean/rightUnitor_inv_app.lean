import Mathlib

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem rightUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).inv.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv :=
  rfl

