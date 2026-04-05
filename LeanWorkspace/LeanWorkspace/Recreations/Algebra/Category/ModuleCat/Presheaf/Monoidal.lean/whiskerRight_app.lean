import Mathlib

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem whiskerRight_app (f : M₁ ⟶ M₂) (M₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    dsimp% (f ▷ M₃).app X = whiskerRight (C := ModuleCat (R.obj X)) (f.app X) (M₃.obj X) := rfl

