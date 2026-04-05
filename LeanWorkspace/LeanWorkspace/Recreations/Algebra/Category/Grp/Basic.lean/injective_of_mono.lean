import Mathlib

theorem injective_of_mono {G H : AddCommGrpCat.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f := fun g₁ g₂ h => by
  have t0 : AddCommGrpCat.asHom g₁ ≫ f = AddCommGrpCat.asHom g₂ ≫ f := by cat_disch
  have t1 : AddCommGrpCat.asHom g₁ = AddCommGrpCat.asHom g₂ := (cancel_mono _).1 t0
  apply AddCommGrpCat.asHom_injective t1

