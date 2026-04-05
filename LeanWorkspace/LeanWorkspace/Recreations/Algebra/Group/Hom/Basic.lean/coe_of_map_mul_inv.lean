import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [Group G]

theorem coe_of_map_mul_inv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : ↑(MonoidHom.ofMapMulInv f map_div) = f := rfl

