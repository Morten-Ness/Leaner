import Mathlib

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem leftUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).inv.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv := by
  rfl

