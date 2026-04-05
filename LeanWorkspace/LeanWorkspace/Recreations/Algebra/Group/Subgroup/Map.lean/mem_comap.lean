import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem mem_comap {K : Subgroup N} {f : G →* N} {x : G} : x ∈ K.comap f ↔ f x ∈ K := Iff.rfl

