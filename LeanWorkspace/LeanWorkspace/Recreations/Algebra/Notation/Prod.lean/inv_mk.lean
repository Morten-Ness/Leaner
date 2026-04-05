import Mathlib

variable {G H M N P R S : Type*}

variable {G H : Type*} [Inv G] [Inv H]

theorem inv_mk (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) := rfl

