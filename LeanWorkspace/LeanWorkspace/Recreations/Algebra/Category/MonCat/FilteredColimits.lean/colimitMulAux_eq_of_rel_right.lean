import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimitMulAux_eq_of_rel_right {x y y' : Σ j, F.obj j}
    (hyy' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) y y') :
    MonCat.FilteredColimits.colimitMulAux.{v, u} F x y = MonCat.FilteredColimits.colimitMulAux.{v, u} F x y' := by
  obtain ⟨j₁, y⟩ := y; obtain ⟨j₂, x⟩ := x; obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp only [Functor.comp_obj, Functor.comp_map, forget_map] at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (IsFiltered.leftToMax j₂ j₁)
      (IsFiltered.leftToMax j₂ j₃) (IsFiltered.rightToMax j₂ j₃) f g
  apply MonCat.FilteredColimits.M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

