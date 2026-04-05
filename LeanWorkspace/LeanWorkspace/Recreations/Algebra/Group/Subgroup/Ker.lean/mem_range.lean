import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem mem_range {f : G →* N} {y : N} : y ∈ f.range ↔ ∃ x, f x = y := Iff.rfl

