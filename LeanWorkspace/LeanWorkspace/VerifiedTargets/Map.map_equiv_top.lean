import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_equiv_top {F : Type*} [EquivLike F G N] [MulEquivClass F G N] (f : F) :
    Subgroup.map (f : G →* N) ⊤ = ⊤ := Subgroup.map_top_of_surjective _ (EquivLike.surjective f)

