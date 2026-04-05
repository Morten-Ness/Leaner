import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_singleton_one : Subgroup.closure ({1} : Set G) = ⊥ := by
  simp [Subgroup.eq_bot_iff_forall, Subgroup.mem_closure_singleton]

