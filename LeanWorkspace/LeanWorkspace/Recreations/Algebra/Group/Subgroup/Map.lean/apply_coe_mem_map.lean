import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem apply_coe_mem_map (f : G →* N) (K : Subgroup G) (x : K) : f x ∈ K.map f := Subgroup.mem_map_of_mem f x.prop

