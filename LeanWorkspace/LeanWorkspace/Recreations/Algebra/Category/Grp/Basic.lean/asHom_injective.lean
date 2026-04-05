import Mathlib

theorem asHom_injective {G : AddCommGrpCat.{0}} : Function.Injective (@AddCommGrpCat.asHom G) := fun h k w => by
  simpa using CategoryTheory.congr_fun w 1

