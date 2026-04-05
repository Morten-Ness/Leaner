import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem nontrivial_iff_exists_ne_one (H : Subgroup G) : Nontrivial H ↔ ∃ x ∈ H, x ≠ (1 : G) := by
  rw [Subtype.nontrivial_iff_exists_ne (fun x => x ∈ H) (1 : H)]
  simp

