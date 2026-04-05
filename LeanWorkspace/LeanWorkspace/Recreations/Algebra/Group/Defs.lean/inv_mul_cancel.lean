import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 := Group.inv_mul_cancel a

