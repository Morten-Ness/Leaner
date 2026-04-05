import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem range_comp (g : N →* P) (f : G →* N) : (g.comp f).range = f.range.map g := (MonoidHom.map_range ..).symm

