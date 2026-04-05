import Mathlib

variable {G H M N P R S : Type*}

variable {G H : Type*} [Div G] [Div H]

theorem fst_div (a b : G × H) : (a / b).1 = a.1 / b.1 := rfl

