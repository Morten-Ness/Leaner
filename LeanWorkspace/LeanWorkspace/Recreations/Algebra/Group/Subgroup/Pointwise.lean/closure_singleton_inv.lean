import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem closure_singleton_inv (x : G) : closure {x⁻¹} = closure {x} := by
  rw [← Set.inv_singleton, Subgroup.closure_inv]

