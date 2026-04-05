import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem map_range (g : N →* P) (f : G →* N) : f.range.map g = (g.comp f).range := by
  rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map]; exact (⊤ : Subgroup G).map_map g f

