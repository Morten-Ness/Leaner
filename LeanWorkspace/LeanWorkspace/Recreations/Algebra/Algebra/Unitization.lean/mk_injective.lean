import Mathlib

variable {R A : Type*}

theorem mk_injective : (Unitization.mk : R × A → Unitization R A).Injective := Unitization.equiv.symm.injective

