import Mathlib

variable {G H M N P R S : Type*}

variable {G H : Type*} [Inv G] [Inv H]

theorem snd_inv (p : G × H) : p⁻¹.2 = p.2⁻¹ := rfl

