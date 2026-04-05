import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem mem_zpowers_iff {g h : G} : h ∈ Subgroup.zpowers g ↔ ∃ k : ℤ, g ^ k = h := Iff.rfl

