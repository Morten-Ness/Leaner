import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem map_normalizer_eq_of_bijective (H : Subgroup G) {f : G →* N} (hf : Function.Bijective f) :
    (normalizer H).map f = normalizer (H.map f) := Subgroup.map_equiv_normalizer_eq H (MulEquiv.ofBijective f hf)

