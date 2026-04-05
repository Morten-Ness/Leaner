import Mathlib

variable {R A : Type*}

theorem inl_injective [Zero A] : Function.Injective (Unitization.inl : R → Unitization R A) := Function.LeftInverse.injective (g := Prod.fst ∘ toProd) <| Unitization.fst_inl _

