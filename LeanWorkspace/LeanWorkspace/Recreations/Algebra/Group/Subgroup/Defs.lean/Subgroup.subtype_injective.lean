import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem subtype_injective (s : Subgroup G) :
    Function.Injective s.subtype := Subtype.coe_injective

