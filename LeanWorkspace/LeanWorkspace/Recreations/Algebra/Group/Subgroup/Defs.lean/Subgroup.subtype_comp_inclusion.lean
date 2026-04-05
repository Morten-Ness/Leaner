import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem subtype_comp_inclusion {H K : Subgroup G} (hH : H ≤ K) :
    K.subtype.comp (Subgroup.inclusion hH) = H.subtype := rfl

