import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem mul_mem_cancel_right {x y : G} (h : x ∈ H) : y * x ∈ H ↔ y ∈ H := mul_mem_cancel_right h

