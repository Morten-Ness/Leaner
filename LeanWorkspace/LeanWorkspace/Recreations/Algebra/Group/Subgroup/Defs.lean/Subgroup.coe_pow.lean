import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem coe_pow (x : H) (n : ℕ) : ((x ^ n : H) : G) = (x : G) ^ n := rfl

