import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem notMem_of_notMem_closure {P : G} (hP : P ∉ Subgroup.closure k) : P ∉ k := fun h =>
  hP (Subgroup.subset_closure h)

