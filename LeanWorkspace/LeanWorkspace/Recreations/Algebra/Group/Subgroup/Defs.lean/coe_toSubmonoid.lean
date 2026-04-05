import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem coe_toSubmonoid (K : Subgroup G) : (K.toSubmonoid : Set G) = K := rfl

