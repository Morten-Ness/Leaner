import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_inf {p p' : Subgroup G} {x : G} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := Iff.rfl

