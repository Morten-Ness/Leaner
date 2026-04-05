import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subgroup G → Submonoid G) := fun p q h => by
    have := SetLike.ext'_iff.1 h
    rw [Subgroup.coe_toSubmonoid, Subgroup.coe_toSubmonoid] at this
    exact SetLike.ext'_iff.2 this

