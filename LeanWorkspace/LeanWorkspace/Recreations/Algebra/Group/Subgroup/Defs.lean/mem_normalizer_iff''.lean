import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem mem_normalizer_iff'' {g : G} : g ∈ Subgroup.normalizer H ↔ ∀ h : G, h ∈ H ↔ g⁻¹ * h * g ∈ H := by
  rw [← Subgroup.inv_mem_iff (x := g), Subgroup.mem_normalizer_iff, inv_inv]

