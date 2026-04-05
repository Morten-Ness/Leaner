import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem presheaf_obj_coe (X : Cᵒᵖ) :
    (M.presheaf.obj X : Type _) = M.obj X := rfl

