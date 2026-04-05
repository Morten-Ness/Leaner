import Mathlib

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]

variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u}) (α : (Functor.const _).obj R ⟶ F)

variable {S : CommRingCat.{u}} (f : R ⟶ S) (c : Cocone F) (hc : IsColimit c)

variable [PreservesColimit F (forget CommRingCat)]

theorem CommRingCat.isFinitelyPresentable_under (S : Under R) (hS : S.hom.hom.FinitePresentation) :
    IsFinitelyPresentable.{u} S := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  exact preservesFilteredColimits_coyoneda R S hS

