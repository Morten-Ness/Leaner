import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem unitHomEquiv_comp_apply {M N : SheafOfModules.{u} R}
    (f : SheafOfModules.unit R ⟶ M) (p : M ⟶ N) :
    N.unitHomEquiv (f ≫ p) = sectionsMap p (M.unitHomEquiv f) := rfl

