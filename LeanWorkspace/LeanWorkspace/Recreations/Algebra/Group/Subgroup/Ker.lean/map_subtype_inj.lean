import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_subtype_inj {H : Subgroup G} {K L : Subgroup H} :
    K.map H.subtype = L.map H.subtype ↔ K = L := MonoidHom.eq_iff (Subgroup.map_injective H.subtype_injective)

