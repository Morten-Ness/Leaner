import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem closure_inv (s : Set G) : closure s⁻¹ = closure s := by
  simp only [← toSubmonoid_inj, Subgroup.closure_toSubmonoid, inv_inv, union_comm]

