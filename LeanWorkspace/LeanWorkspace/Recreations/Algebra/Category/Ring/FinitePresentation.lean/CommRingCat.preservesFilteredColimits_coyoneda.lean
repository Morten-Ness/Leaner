import Mathlib

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]

variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u}) (α : (Functor.const _).obj R ⟶ F)

variable {S : CommRingCat.{u}} (f : R ⟶ S) (c : Cocone F) (hc : IsColimit c)

variable [PreservesColimit F (forget CommRingCat)]

theorem CommRingCat.preservesFilteredColimits_coyoneda (S : Under R)
    (hS : S.hom.hom.FinitePresentation) :
    PreservesFilteredColimits (coyoneda.obj (.op S)) := ⟨fun _ _ _ ↦ ⟨preservesColimit_coyoneda_of_finitePresentation R S hS _⟩⟩

