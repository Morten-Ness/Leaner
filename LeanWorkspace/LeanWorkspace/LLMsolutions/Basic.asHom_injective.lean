FAIL
import Mathlib

theorem asHom_injective {G : AddCommGrpCat.{0}} : Function.Injective (@AddCommGrpCat.asHom G) := by
  intro a b h
  ext
  exact congrFun h x
