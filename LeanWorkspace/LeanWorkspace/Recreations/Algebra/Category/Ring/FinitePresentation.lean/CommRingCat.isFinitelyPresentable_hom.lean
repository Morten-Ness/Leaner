import Mathlib

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]

variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u}) (α : (Functor.const _).obj R ⟶ F)

variable {S : CommRingCat.{u}} (f : R ⟶ S) (c : Cocone F) (hc : IsColimit c)

variable [PreservesColimit F (forget CommRingCat)]

theorem CommRingCat.isFinitelyPresentable_hom {S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.FinitePresentation) :
    MorphismProperty.isFinitelyPresentable.{u} _ f := isFinitelyPresentable_under R (Under.mk f) hf

