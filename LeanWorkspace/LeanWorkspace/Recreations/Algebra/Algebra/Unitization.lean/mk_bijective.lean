import Mathlib

variable {R A : Type*}

theorem mk_bijective : (Unitization.mk : R × A → Unitization R A).Bijective := Unitization.equiv.symm.bijective

