import Mathlib

variable {R A : Type*}

theorem inr_injective [Zero R] : Function.Injective ((↑) : A → Unitization R A) := Function.LeftInverse.injective (g := Prod.snd ∘ toProd) <| Unitization.snd_inr _

