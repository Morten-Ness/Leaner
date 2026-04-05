import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem toPresheaf_obj_coe (X : Cᵒᵖ) :
    (((PresheafOfModules.toPresheaf R).obj M).obj X : Type _) = M.obj X := rfl

