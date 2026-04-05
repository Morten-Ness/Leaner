import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Inv (G i)]

variable {G : Type*} [Inv G]

theorem _root_.Function.const_inv (a : G) : (const ι a)⁻¹ = const ι a⁻¹ := rfl

