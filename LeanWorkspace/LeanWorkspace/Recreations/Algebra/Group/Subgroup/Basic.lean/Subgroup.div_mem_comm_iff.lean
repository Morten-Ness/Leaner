import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem div_mem_comm_iff {a b : G} : a / b ∈ H ↔ b / a ∈ H := div_mem_comm_iff

