import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Mul (M i)]

variable {M : Type*} [Mul M]

theorem _root_.Function.const_mul (a b : M) : const ι a * const ι b = const ι (a * b) := rfl

