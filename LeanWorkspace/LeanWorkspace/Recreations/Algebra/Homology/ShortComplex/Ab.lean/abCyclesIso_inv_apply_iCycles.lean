import Mathlib

variable (S : ShortComplex Ab.{u})

set_option backward.isDefEq.respectTransparency false in
theorem abCyclesIso_inv_apply_iCycles (x : AddMonoidHom.ker S.g.hom) :
    S.iCycles (S.abCyclesIso.inv x) = x := by
  dsimp only [CategoryTheory.ShortComplex.abCyclesIso]
  rw [← ConcreteCategory.comp_apply, S.abLeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl

