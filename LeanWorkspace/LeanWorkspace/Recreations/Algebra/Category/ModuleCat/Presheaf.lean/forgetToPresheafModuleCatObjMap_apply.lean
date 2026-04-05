import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

variable (X : Cᵒᵖ) (hX : Limits.IsInitial X)

variable (M : PresheafOfModules.{v} R)

theorem forgetToPresheafModuleCatObjMap_apply {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (m : M.obj Y) :
    (PresheafOfModules.forgetToPresheafModuleCatObjMap X hX M f).hom m = M.map f m := rfl

