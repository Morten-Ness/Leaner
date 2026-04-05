import Mathlib

section

variable {G : Type*} [Group G] (H : Subgroup G)

theorem isCoatom_comap {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup H} :
    IsCoatom (Subgroup.comap (f : G →* H) K) ↔ IsCoatom K := OrderIso.isCoatom_iff (f.comapSubgroup) K

end

section

variable {G : Type*} [Group G] (H : Subgroup G)

theorem isCoatom_map (f : G ≃* H) {K : Subgroup G} :
    IsCoatom (Subgroup.map (f : G →* H) K) ↔ IsCoatom K := OrderIso.isCoatom_iff (f.mapSubgroup) K

end
