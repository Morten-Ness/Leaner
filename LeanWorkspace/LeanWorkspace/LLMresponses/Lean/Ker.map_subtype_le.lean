import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_le {H : Subgroup G} (K : Subgroup H) : K.map H.subtype ≤ H := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.property
