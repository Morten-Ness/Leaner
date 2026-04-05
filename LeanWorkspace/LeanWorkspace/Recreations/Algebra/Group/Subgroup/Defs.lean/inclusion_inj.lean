import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem inclusion_inj {H K : Subgroup G} (h : H ≤ K) {x y : H} :
    Subgroup.inclusion h x = Subgroup.inclusion h y ↔ x = y := (Subgroup.inclusion_injective h).eq_iff

