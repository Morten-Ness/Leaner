import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem quotUliftToQuot_ι [DecidableEq J] (j : J) (x : (F ⋙ uliftFunctor.{u'}).obj j) :
    AddCommGrpCat.Colimits.quotUliftToQuot F (AddCommGrpCat.Colimits.Quot.ι _ j x) = AddCommGrpCat.Colimits.Quot.ι F j x.down := by
  dsimp [AddCommGrpCat.Colimits.quotUliftToQuot, AddCommGrpCat.Colimits.Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations (F ⋙ uliftFunctor)))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [Functor.comp_obj, uliftFunctor_obj, DFinsupp.singleAddHom_apply,
    DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply]
  rfl

