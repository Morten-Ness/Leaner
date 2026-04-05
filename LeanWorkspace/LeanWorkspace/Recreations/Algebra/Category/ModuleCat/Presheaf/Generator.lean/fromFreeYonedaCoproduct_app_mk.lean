import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem fromFreeYonedaCoproduct_app_mk (m : M.Elements) :
    M.fromFreeYonedaCoproduct.app _ (M.freeYonedaCoproductMk m) = m.2 := by
  dsimp [PresheafOfModules.freeYonedaCoproductMk]
  erw [M.ι_fromFreeYonedaCoproduct_apply m]
  rw [PresheafOfModules.Elements.fromFreeYoneda_app_apply m]

