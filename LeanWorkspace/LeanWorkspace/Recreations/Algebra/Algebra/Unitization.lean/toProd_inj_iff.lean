import Mathlib

variable {R A : Type*}

theorem toProd_inj_iff {x y : Unitization R A} : toProd x = toProd y ↔ x = y := Unitization.toProd_injective.eq_iff

