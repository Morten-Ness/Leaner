import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.ι_desc [DecidableEq J] (j : J) (x : F.obj j) :
    AddCommGrpCat.Colimits.Quot.desc F c (AddCommGrpCat.Colimits.Quot.ι F j x) = c.ι.app j x := by
  dsimp [desc, ι]
  erw [QuotientAddGroup.lift_mk']
  simp

