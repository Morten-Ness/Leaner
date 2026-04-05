import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

theorem quotToQuotUlift_ι [DecidableEq J] (j : J) (x : F.obj j) :
    AddCommGrpCat.Colimits.quotToQuotUlift F (AddCommGrpCat.Colimits.Quot.ι F j x) = AddCommGrpCat.Colimits.Quot.ι _ j (ULift.up x) := by
  dsimp [AddCommGrpCat.Colimits.quotToQuotUlift, AddCommGrpCat.Colimits.Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations F))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_coe, Function.comp_apply]
  rfl

