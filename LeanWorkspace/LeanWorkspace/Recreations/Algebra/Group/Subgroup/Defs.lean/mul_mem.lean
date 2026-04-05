import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := mul_mem

