import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

variable {M N P Q : AddSubmonoid R}

variable {ι : Sort*}

theorem mul_iSup (T : AddSubmonoid R) (S : ι → AddSubmonoid R) : (T * ⨆ i, S i) = ⨆ i, T * S i := AddSubmonoid.smul_iSup T S

