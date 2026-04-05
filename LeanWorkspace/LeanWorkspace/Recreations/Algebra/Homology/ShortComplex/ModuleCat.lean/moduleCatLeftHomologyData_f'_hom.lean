import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCatLeftHomologyData_f'_hom :
    S.moduleCatLeftHomologyData.f'.hom = S.moduleCatToCycles := rfl

