import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H := mul_mem_cancel_left h

