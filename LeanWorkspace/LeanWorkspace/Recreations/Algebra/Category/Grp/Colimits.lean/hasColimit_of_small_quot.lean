import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

theorem hasColimit_of_small_quot [DecidableEq J] (h : Small.{w} (AddCommGrpCat.Colimits.Quot F)) : HasColimit F := ⟨_, AddCommGrpCat.Colimits.colimitCoconeIsColimit F⟩

