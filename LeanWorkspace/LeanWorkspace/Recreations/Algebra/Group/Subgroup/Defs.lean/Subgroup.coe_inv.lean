import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem coe_inv (x : H) : ↑(x⁻¹ : H) = (x⁻¹ : G) := rfl

