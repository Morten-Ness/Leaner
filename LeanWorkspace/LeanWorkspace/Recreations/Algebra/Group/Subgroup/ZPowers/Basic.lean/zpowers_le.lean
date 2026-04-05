import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {s : Set G} {g : G}

theorem zpowers_le {g : G} {H : Subgroup G} : Subgroup.zpowers g ≤ H ↔ g ∈ H := by
  rw [Subgroup.zpowers_eq_closure, closure_le, Set.singleton_subset_iff, SetLike.mem_coe]

