import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {s : Set G} {g : G}

theorem zpowers_eq_bot {g : G} : Subgroup.zpowers g = ⊥ ↔ g = 1 := by rw [eq_bot_iff, Subgroup.zpowers_le, mem_bot]

