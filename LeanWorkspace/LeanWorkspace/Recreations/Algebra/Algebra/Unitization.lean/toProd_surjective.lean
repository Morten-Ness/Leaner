import Mathlib

variable {R A : Type*}

theorem toProd_surjective : (toProd : Unitization R A → R × A).Surjective := Unitization.equiv.surjective

