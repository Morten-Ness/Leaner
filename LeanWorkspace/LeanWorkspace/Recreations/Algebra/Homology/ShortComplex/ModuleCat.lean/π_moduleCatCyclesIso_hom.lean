import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem π_moduleCatCyclesIso_hom :
    S.homologyπ ≫ S.moduleCatHomologyIso.hom =
      S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π := S.moduleCatLeftHomologyData.homologyπ_comp_homologyIso_hom

