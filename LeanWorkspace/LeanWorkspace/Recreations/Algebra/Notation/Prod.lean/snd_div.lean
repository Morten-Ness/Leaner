import Mathlib

variable {G H M N P R S : Type*}

variable {G H : Type*} [Div G] [Div H]

theorem snd_div (a b : G × H) : (a / b).2 = a.2 / b.2 := rfl

