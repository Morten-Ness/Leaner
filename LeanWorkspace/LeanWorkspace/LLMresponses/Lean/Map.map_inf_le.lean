import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf_le (H K : Subgroup G) (f : G →* N) : Subgroup.map f (H ⊓ K) ≤ Subgroup.map f H ⊓ Subgroup.map f K := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
