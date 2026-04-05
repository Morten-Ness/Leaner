import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem map_eq_comap_of_inverse {f : G →* N} {g : N →* G} (hl : Function.LeftInverse g f)
    (hr : Function.RightInverse g f) (H : Subgroup G) : Subgroup.map f H = Subgroup.comap g H := SetLike.ext' <| by rw [Subgroup.coe_map, Subgroup.coe_comap, Set.image_eq_preimage_of_inverse hl hr]

