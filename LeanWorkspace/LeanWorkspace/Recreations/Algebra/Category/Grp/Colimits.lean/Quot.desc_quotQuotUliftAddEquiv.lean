import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.desc_quotQuotUliftAddEquiv [DecidableEq J] (c : Cocone F) :
    (AddCommGrpCat.Colimits.Quot.desc (F ⋙ uliftFunctor.{u'}) (uliftFunctor.{u'}.mapCocone c)).comp
    (AddCommGrpCat.Colimits.quotQuotUliftAddEquiv F).toAddMonoidHom =
    AddEquiv.ulift.symm.toAddMonoidHom.comp (AddCommGrpCat.Colimits.Quot.desc F c) := by
  refine AddCommGrpCat.Colimits.Quot.addMonoidHom_ext _ (fun j a ↦ ?_)
  dsimp
  simp only [AddCommGrpCat.Colimits.quotToQuotUlift_ι, Functor.comp_obj, uliftFunctor_obj, ι_desc, Functor.const_obj_obj,
    ι_desc]
  erw [AddCommGrpCat.Colimits.Quot.ι_desc]
  rfl

