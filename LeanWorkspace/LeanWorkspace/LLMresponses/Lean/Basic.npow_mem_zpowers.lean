import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem npow_mem_zpowers (g : G) (k : ℕ) : g ^ k ∈ Subgroup.zpowers g := by
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, by simp⟩
