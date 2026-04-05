import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {s : Set G} {g : G}

theorem zpowers_one_eq_bot : Subgroup.zpowers (1 : G) = ⊥ := Subgroup.zpowers_eq_bot.mpr rfl

