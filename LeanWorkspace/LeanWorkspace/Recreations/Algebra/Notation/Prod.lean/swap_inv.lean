import Mathlib

variable {G H M N P R S : Type*}

variable {G H : Type*} [Inv G] [Inv H]

theorem swap_inv (p : G × H) : p⁻¹.swap = p.swap⁻¹ := rfl

