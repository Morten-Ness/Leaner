import Mathlib

variable {R A : Type*}

theorem toProd_injective : (toProd : Unitization R A → R × A).Injective := Unitization.equiv.injective

