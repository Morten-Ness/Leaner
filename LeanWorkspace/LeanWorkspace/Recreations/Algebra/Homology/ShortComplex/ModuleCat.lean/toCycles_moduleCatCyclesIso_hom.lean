import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

set_option backward.isDefEq.respectTransparency false in
theorem toCycles_moduleCatCyclesIso_hom :
    S.toCycles ≫ S.moduleCatCyclesIso.hom = S.moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono S.moduleCatLeftHomologyData.i]

