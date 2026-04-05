import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {s : Set G} {g : G}

theorem zpowers_ne_bot : Subgroup.zpowers g ≠ ⊥ ↔ g ≠ 1 := Subgroup.zpowers_eq_bot.not

