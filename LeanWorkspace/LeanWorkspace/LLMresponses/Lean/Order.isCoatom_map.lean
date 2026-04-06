import Mathlib

variable {G : Type*} [Group G] (H : Subgroup G)

theorem isCoatom_map (f : G ≃* H) {K : Subgroup G} :
    IsCoatom (Subgroup.map (f : G →* H) K) ↔ IsCoatom K := by
  simpa using OrderIso.isCoatom_iff (Subgroup.comapMkEquiv f) K
