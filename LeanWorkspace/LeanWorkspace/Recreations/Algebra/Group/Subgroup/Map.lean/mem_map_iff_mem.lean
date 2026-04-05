import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem mem_map_iff_mem {f : G →* N} (hf : Function.Injective f) {K : Subgroup G} {x : G} :
    f x ∈ K.map f ↔ x ∈ K := hf.mem_set_image

