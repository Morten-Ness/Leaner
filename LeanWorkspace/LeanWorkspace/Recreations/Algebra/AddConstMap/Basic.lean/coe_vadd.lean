import Mathlib

variable {G H : Type*} [Add G] [Add H] {a : G} {b : H}

theorem coe_vadd {K : Type*} [VAdd K H] [VAddAssocClass K H H] (c : K) (f : G →+c[a, b] H) :
    ⇑(c +ᵥ f) = c +ᵥ ⇑f := rfl

