import Mathlib

variable {G H M N P R S : Type*}

variable {G H : Type*} [Inv G] [Inv H]

theorem fst_inv (p : G × H) : p⁻¹.1 = p.1⁻¹ := rfl

