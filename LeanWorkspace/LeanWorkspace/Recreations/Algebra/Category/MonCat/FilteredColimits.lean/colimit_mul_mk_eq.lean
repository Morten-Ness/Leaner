import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk.{v, u} F x * M.mk F y = M.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  refine MonCat.FilteredColimits.M.mk_eq F _ _ ?_
  use s, α, β
  dsimp
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂]

