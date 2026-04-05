import Mathlib

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • ModuleCat.FilteredColimits.M.mk F x = ModuleCat.FilteredColimits.M.mk F ⟨x.1, r • x.2⟩ := rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): writing directly the `Module` instance makes things very slow.

