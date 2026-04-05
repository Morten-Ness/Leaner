import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem coe_zpow (x : H) (n : ℤ) : ((x ^ n : H) : G) = (x : G) ^ n := by
  dsimp

