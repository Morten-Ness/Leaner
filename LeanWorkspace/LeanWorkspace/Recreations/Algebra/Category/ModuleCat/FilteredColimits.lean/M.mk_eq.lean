import Mathlib

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : ModuleCat.FilteredColimits.M.mk F x = ModuleCat.FilteredColimits.M.mk F y := Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
    (F ⋙ forget (ModuleCat R)) x y h)

