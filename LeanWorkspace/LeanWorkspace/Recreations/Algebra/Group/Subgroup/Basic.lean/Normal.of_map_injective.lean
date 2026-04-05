import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Normal.of_map_injective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {L : Subgroup G} (n : (L.map φ).Normal) : L.Normal := L.comap_map_eq_self_of_injective hφ ▸ n.comap φ

