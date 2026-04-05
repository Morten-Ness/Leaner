import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

theorem toFreeYonedaCoproduct_fromFreeYonedaCoproduct :
    M.toFreeYonedaCoproduct ≫ M.fromFreeYonedaCoproduct = 0 := by
  simp [PresheafOfModules.toFreeYonedaCoproduct]

