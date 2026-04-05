import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem div_mem {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x / y ∈ H := div_mem hx hy

