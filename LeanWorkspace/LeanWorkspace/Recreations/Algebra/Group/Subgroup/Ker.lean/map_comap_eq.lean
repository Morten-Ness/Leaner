import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_comap_eq (H : Subgroup N) : map f (comap f H) = f.range ⊓ H := SetLike.ext' <| by
    rw [coe_map, coe_comap, Set.image_preimage_eq_inter_range, coe_inf, MonoidHom.coe_range, Set.inter_comm]

