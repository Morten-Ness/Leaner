import Mathlib

variable {R A : Type*}

theorem mk_surjective : (Unitization.mk : R × A → Unitization R A).Surjective := Unitization.equiv.symm.surjective

