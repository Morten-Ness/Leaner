import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
theorem QuasicoherentData.isQuasicoherent {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    M.IsQuasicoherent := ⟨⟨q.shrink⟩⟩

