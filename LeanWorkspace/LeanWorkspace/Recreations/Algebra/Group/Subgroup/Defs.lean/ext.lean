import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem ext {H K : Subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := SetLike.ext h

