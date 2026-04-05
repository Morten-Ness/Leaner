import Mathlib

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pullbackObjIsDefined_free_yoneda (X : C) :
    pullbackObjIsDefined φ ((free S).obj (yoneda.obj X)) := (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).isCorepresentable

