import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

variable (F : C ⥤ D) [F.Additive]

theorem mapHomologicalComplex_commShiftIso_inv_app_f (K : CochainComplex C ℤ) (n i : ℤ) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).inv.app K).f i = 𝟙 _ := rfl

