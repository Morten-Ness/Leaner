import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

variable {M N P Q : AddSubmonoid R}

theorem mul_le_mul_left (h : M ≤ N) : M * P ≤ N * P := AddSubmonoid.smul_le_smul_left h

