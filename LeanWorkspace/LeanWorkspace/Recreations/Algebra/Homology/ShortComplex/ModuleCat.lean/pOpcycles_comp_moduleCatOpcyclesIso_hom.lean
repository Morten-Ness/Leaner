import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem pOpcycles_comp_moduleCatOpcyclesIso_hom :
    S.pOpcycles ≫ S.moduleCatOpcyclesIso.hom = ModuleCat.ofHom (Submodule.mkQ _) := by
  simp [CategoryTheory.ShortComplex.moduleCatOpcyclesIso]

