import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_closure_singleton_self (x : G) : x ∈ Subgroup.closure ({x} : Set G) := by
  simpa [-Subgroup.subset_closure] using Subgroup.subset_closure (k := {x})

