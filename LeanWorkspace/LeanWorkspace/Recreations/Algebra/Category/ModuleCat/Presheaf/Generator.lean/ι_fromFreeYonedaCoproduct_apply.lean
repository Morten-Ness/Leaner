import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

theorem ι_fromFreeYonedaCoproduct_apply (m : M.Elements) (X : Cᵒᵖ) (x : m.freeYoneda.obj X) :
    M.fromFreeYonedaCoproduct.app X ((M.ιFreeYonedaCoproduct m).app X x) =
      m.fromFreeYoneda.app X x := congr_fun ((evaluation R X ⋙ forget _).congr_map (M.ι_fromFreeYonedaCoproduct m)) x

