import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCatCyclesIso_inv_iCycles :
    S.moduleCatCyclesIso.inv ≫ S.iCycles = S.moduleCatLeftHomologyData.i := S.moduleCatLeftHomologyData.cyclesIso_inv_comp_iCycles

