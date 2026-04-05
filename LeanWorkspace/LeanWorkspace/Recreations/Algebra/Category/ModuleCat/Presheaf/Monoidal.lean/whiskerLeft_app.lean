import Mathlib

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem whiskerLeft_app (f : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    dsimp% (M₁ ◁ f).app X = whiskerLeft (C := ModuleCat (R.obj X)) (M₁.obj X) (f.app X) :=
  rfl

