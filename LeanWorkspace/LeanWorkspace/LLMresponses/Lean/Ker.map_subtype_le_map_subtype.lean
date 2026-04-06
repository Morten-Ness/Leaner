import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_le_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype ≤ K.map G'.subtype ↔ H ≤ K := by
  constructor
  · intro h x hx
    rcases h ⟨x, hx, rfl⟩ with ⟨y, hy, hxy⟩
    exact by
      cases Subtype.ext hxy
      exact hy
  · intro h x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, h hy, rfl⟩
