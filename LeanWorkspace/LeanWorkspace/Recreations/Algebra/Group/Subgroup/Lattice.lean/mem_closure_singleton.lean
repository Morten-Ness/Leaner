import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_closure_singleton {x y : G} : y ∈ Subgroup.closure ({x} : Set G) ↔ ∃ n : ℤ, x ^ n = y := by
  refine
    ⟨fun hy => Subgroup.closure_induction ?_ ?_ ?_ ?_ hy, fun ⟨n, hn⟩ =>
      hn ▸ zpow_mem (Subgroup.subset_closure <| mem_singleton x) n⟩
  · intro y hy
    rw [eq_of_mem_singleton hy]
    exact ⟨1, zpow_one x⟩
  · exact ⟨0, zpow_zero x⟩
  · rintro _ _ _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, zpow_add x n m⟩
  rintro _ _ ⟨n, rfl⟩
  exact ⟨-n, zpow_neg x n⟩

