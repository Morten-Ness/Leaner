import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_le (H : Subgroup G) : H.normalCore ≤ H := fun a h => by
  rw [← mul_one a, ← inv_one, ← one_mul a]
  exact h 1

