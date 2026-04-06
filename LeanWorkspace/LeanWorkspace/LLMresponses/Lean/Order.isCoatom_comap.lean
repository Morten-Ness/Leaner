import Mathlib

variable {G : Type*} [Group G] (H : Subgroup G)

theorem isCoatom_comap {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup H} :
    IsCoatom (Subgroup.comap (f : G →* H) K) ↔ IsCoatom K := by
  simpa using f.toOrderIso.isCoatom_iff' (a := Subgroup.comap (f : G →* H) K)
