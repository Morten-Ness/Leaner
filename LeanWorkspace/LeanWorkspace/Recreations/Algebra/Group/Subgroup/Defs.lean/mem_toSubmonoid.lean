import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem mem_toSubmonoid (K : Subgroup G) (x : G) : x ∈ K.toSubmonoid ↔ x ∈ K := Iff.rfl

