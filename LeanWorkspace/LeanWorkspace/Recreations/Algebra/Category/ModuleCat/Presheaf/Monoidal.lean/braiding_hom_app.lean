import Mathlib

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem braiding_hom_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).hom.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).hom := by
  rfl

