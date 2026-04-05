import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

variable [Group G]

theorem mem_closure_inv (s : Set G) (x : G) : x ∈ closure s⁻¹ ↔ x⁻¹ ∈ closure s := by
  rw [Submonoid.closure_inv, Submonoid.mem_inv]

