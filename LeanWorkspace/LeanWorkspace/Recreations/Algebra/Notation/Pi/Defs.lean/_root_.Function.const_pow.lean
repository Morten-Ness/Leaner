import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Pow (M i) α]

variable {M : Type*} [Pow M α]

theorem _root_.Function.const_pow (a : M) (b : α) : const ι a ^ b = const ι (a ^ b) := rfl

