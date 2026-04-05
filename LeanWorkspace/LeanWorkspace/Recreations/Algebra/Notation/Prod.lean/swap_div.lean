import Mathlib

variable {G H M N P R S : Type*}

variable {G H : Type*} [Div G] [Div H]

theorem swap_div (a b : G × H) : (a / b).swap = a.swap / b.swap := rfl

