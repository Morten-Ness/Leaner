import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_closure_of_mem {s : Set G} {x : G} (hx : x ∈ s) : x ∈ Subgroup.closure s := Subgroup.subset_closure hx

