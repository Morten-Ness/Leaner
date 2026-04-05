import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.of_map_subtype {K : Subgroup G} {L : Subgroup K}
    (n : (Subgroup.map K.subtype L).Normal) : L.Normal := n.of_map_injective K.subtype_injective

