import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

theorem map_eq_bot_iff {f : G →* N} : H.map f = ⊥ ↔ H ≤ f.ker := (gc_map_comap f).l_eq_bot

