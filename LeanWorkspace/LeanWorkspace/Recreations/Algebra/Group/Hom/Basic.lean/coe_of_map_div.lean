import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [Group G]

theorem coe_of_map_div {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) :
    ↑(MonoidHom.ofMapDiv f hf) = f := rfl

