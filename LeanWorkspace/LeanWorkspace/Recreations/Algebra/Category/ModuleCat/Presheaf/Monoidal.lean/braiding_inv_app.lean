import Mathlib

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem braiding_inv_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).inv.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).inv := rfl

