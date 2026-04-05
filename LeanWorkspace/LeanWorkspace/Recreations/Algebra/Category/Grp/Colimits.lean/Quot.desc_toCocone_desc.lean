import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.desc_toCocone_desc [DecidableEq J] {A : Type w} [AddCommGroup A] (f : AddCommGrpCat.Colimits.Quot F →+ A)
    (hc : IsColimit c) : (hc.desc (AddCommGrpCat.Colimits.toCocone F f)).hom.comp (AddCommGrpCat.Colimits.Quot.desc F c) = f := by
  refine AddCommGrpCat.Colimits.Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  rw [AddMonoidHom.comp_apply, ι_desc]
  change (c.ι.app j ≫ hc.desc (AddCommGrpCat.Colimits.toCocone F f)) _ = _
  rw [hc.fac]
  simp

