import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCatCyclesIso_inv_π :
    S.moduleCatCyclesIso.inv ≫ S.homologyπ =
       S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv := S.moduleCatLeftHomologyData.π_comp_homologyIso_inv

