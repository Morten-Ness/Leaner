import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem coe_zpowers (g : G) : ↑(Subgroup.zpowers g) = Set.range (g ^ · : ℤ → G) := rfl

