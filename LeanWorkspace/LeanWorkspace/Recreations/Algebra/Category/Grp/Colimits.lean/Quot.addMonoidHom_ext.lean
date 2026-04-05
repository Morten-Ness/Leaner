import Mathlib

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

theorem Quot.addMonoidHom_ext [DecidableEq J] {α : Type*} [AddMonoid α] {f g : AddCommGrpCat.Colimits.Quot F →+ α}
    (h : ∀ (j : J) (x : F.obj j), f (AddCommGrpCat.Colimits.Quot.ι F j x) = g (AddCommGrpCat.Colimits.Quot.ι F j x)) : f = g := QuotientAddGroup.addMonoidHom_ext _ (DFinsupp.addHom_ext h)

