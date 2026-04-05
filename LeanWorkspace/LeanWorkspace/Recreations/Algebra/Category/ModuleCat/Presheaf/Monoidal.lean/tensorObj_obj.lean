import Mathlib

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem tensorObj_obj (X : Cᵒᵖ) :
    (M₁ ⊗ M₂).obj X =
      MonoidalCategory.tensorObj (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) := rfl

attribute [local simp] tensorObj_obj

