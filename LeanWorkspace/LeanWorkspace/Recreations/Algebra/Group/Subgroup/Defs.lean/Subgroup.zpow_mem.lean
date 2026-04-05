import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem zpow_mem {x : G} (hx : x ∈ K) : ∀ n : ℤ, x ^ n ∈ K := zpow_mem hx

