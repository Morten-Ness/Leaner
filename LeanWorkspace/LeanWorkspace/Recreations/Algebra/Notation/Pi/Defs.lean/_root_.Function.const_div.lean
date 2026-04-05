import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Div (G i)]

variable {G : Type*} [Div G]

theorem _root_.Function.const_div (a b : G) : const ι a / const ι b = const ι (a / b) := rfl

