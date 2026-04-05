import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem pow_mem {x : G} (hx : x ∈ K) : ∀ n : ℕ, x ^ n ∈ K := pow_mem hx

