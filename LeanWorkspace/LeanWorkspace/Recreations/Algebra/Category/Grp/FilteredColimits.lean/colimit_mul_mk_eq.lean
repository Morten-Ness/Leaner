import Mathlib

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    G.mk.{v, u} F x * G.mk F y = G.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ := MonCat.FilteredColimits.colimit_mul_mk_eq _ _ _ _ _ _

