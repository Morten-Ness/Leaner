import Mathlib

variable {G : Type*}

variable [InvOneClass G]

theorem inv_one : (1 : G)⁻¹ = 1 := InvOneClass.inv_one

