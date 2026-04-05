import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

variable (X : Cᵒᵖ) (hX : Limits.IsInitial X)

variable (M : PresheafOfModules.{v} R)

theorem forgetToPresheafModuleCatObjObj_coe (Y : Cᵒᵖ) :
    (forgetToPresheafModuleCatObjObj X hX M Y : Type _) = M.obj Y := rfl

