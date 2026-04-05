import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y := rfl

