import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

variable [Group G]

theorem closure_inv (s : Set G) : closure s⁻¹ = (closure s)⁻¹ := by
  apply le_antisymm
  · rw [closure_le, Submonoid.coe_inv, ← Set.inv_subset, inv_inv]
    exact subset_closure
  · rw [Submonoid.inv_le, closure_le, Submonoid.coe_inv, ← Set.inv_subset]
    exact subset_closure

