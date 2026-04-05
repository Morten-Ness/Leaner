import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCatCyclesIso_hom_i :
    S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.i = S.iCycles := S.moduleCatLeftHomologyData.cyclesIso_hom_comp_i

