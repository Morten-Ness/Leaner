import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem mem_carrier {s : Subgroup G} {x : G} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

