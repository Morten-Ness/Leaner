import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem ker_le_comap (H : Subgroup N) : f.ker ≤ comap f H := MonoidHom.comap_bot f ▸ comap_mono bot_le

