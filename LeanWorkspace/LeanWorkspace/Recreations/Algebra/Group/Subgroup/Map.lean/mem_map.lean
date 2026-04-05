import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem mem_map {f : G →* N} {K : Subgroup G} {y : N} : y ∈ K.map f ↔ ∃ x ∈ K, f x = y := Iff.rfl

