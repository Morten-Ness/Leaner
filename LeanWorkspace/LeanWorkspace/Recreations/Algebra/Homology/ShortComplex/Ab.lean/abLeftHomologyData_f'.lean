import Mathlib

variable (S : ShortComplex Ab.{u})

theorem abLeftHomologyData_f' : S.abLeftHomologyData.f' = AddCommGrpCat.ofHom S.abToCycles := rfl

