import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    (H ⊓ K).map f = H.map f ⊓ K.map f := SetLike.coe_injective (Set.image_inter hf)

