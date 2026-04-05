import Mathlib

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem unitHomEquiv_symm_comp {M N : SheafOfModules.{u} R} (s : M.sections) (p : M ⟶ N) :
    M.unitHomEquiv.symm s ≫ p = N.unitHomEquiv.symm (sectionsMap p s) := N.unitHomEquiv.injective (by simp [SheafOfModules.unitHomEquiv_comp_apply])

end
