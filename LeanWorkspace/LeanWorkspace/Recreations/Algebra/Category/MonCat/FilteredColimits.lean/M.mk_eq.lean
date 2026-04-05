import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    M.mk.{v, u} F x = M.mk F y := Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget MonCat) x y h)

