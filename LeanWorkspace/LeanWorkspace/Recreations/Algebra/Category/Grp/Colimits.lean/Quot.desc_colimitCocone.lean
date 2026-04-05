import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

theorem Quot.desc_colimitCocone [DecidableEq J] (F : J ⥤ AddCommGrpCat.{w}) [Small.{w} (AddCommGrpCat.Colimits.Quot F)] :
    AddCommGrpCat.Colimits.Quot.desc F (AddCommGrpCat.Colimits.colimitCocone F) = (Shrink.addEquiv (α := AddCommGrpCat.Colimits.Quot F)).symm.toAddMonoidHom := by
  refine AddCommGrpCat.Colimits.Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  simpa only [colimitCocone_pt, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    using AddCommGrpCat.Colimits.Quot.ι_desc F (AddCommGrpCat.Colimits.colimitCocone F) j x

