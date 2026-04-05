import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in
theorem Quot.desc_toCocone_desc_app [DecidableEq J] {A : Type w} [AddCommGroup A] (f : AddCommGrpCat.Colimits.Quot F →+ A)
    (hc : IsColimit c) (x : AddCommGrpCat.Colimits.Quot F) : hc.desc (AddCommGrpCat.Colimits.toCocone F f) (AddCommGrpCat.Colimits.Quot.desc F c x) = f x := by
  conv_rhs => rw [← AddCommGrpCat.Colimits.Quot.desc_toCocone_desc F c f hc]
  dsimp

