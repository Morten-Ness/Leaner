import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.map_ι [DecidableEq J] {j j' : J} {f : j ⟶ j'} (x : F.obj j) :
    AddCommGrpCat.Colimits.Quot.ι F j' (F.map f x) = AddCommGrpCat.Colimits.Quot.ι F j x := by
  dsimp [ι]
  refine eq_of_sub_eq_zero ?_
  erw [← (QuotientAddGroup.mk' (Relations F)).map_sub, ← AddMonoidHom.mem_ker]
  rw [QuotientAddGroup.ker_mk']
  simp only [DFinsupp.singleAddHom_apply]
  exact AddSubgroup.subset_closure ⟨j, j', f, x, rfl⟩

