import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

theorem ι_fromFreeYonedaCoproduct (m : M.Elements) :
    M.ιFreeYonedaCoproduct m ≫ M.fromFreeYonedaCoproduct = m.fromFreeYoneda := by
  apply Sigma.ι_desc

