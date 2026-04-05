import Mathlib

variable {R A : Type*}

theorem toProd_bijective : (toProd : Unitization R A → R × A).Bijective := Unitization.equiv.bijective

