import Mathlib

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC] [HasForget₂ C Ab]

variable [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

set_option backward.isDefEq.respectTransparency false in
theorem i_cyclesMk [S.HasHomology] (x₂ : (forget₂ C Ab).obj S.X₂)
    (hx₂ : ((forget₂ C Ab).map S.g) x₂ = 0) :
    (forget₂ C Ab).map S.iCycles (S.cyclesMk x₂ hx₂) = x₂ := by
  dsimp [CategoryTheory.ShortComplex.cyclesMk]
  -- `abCyclesIso_inv_apply_iCycles` is not in `simp`-normal form, so we first
  -- have to simplify it.
  have := abCyclesIso_inv_apply_iCycles (S.map (forget₂ C Ab)) ⟨x₂, hx₂⟩
  simp only [map_X₂, map_X₃, map_g] at this
  rw [← ConcreteCategory.comp_apply, S.mapCyclesIso_hom_iCycles (forget₂ C Ab), this]

