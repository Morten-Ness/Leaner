import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem mem_zpowers (g : G) : g ∈ Subgroup.zpowers g := ⟨1, zpow_one _⟩

