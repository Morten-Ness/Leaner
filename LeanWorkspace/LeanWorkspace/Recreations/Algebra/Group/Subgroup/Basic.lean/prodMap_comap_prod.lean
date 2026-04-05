import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem prodMap_comap_prod {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G →* N)
    (g : G' →* N') (S : Subgroup N) (S' : Subgroup N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) := SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

