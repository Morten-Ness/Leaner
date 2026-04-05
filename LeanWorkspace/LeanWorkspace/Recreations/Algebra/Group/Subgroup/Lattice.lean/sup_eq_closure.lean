import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem sup_eq_closure (H H' : Subgroup G) : H ⊔ H' = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  simp_rw [Subgroup.closure_union, Subgroup.closure_eq]

