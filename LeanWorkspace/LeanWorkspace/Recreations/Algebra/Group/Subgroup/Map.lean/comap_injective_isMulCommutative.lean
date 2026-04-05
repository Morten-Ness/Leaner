import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

variable (H : Subgroup G)

theorem comap_injective_isMulCommutative {f : G' →* G} (hf : Function.Injective f) [IsMulCommutative H] :
    IsMulCommutative (H.comap f) := .of_setLike_mul_comm fun a (ha : f a ∈ H) b (hb : f b ∈ H) ↦ hf <| by
    simpa using setLike_mul_comm ha hb

