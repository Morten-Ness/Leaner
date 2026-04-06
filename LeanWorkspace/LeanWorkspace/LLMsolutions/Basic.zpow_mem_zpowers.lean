import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem zpow_mem_zpowers (g : G) (k : ℤ) : g ^ k ∈ Subgroup.zpowers g := by
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
