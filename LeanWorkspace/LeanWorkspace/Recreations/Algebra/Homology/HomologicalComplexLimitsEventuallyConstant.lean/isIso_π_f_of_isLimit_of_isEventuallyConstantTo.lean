import Mathlib

variable {C J ι : Type*} [Category C] [Category J]
   {c : ComplexShape ι} [IsCofiltered J]

variable [HasZeroMorphisms C] (F : J ⥤ HomologicalComplex C c)
  [∀ (j : ι), HasLimit (F ⋙ eval C c j)]
  {cF : Cone F} (hcF : IsLimit cF)

theorem isIso_π_f_of_isLimit_of_isEventuallyConstantTo
    (q : ι) (j : J) (hq : (F ⋙ eval C c q).IsEventuallyConstantTo j) :
    IsIso ((cF.π.app j).f q) := hq.isIso_π_of_isLimit (isLimitOfPreserves (eval C c q) hcF)

