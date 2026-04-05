import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

variable {M N P Q : AddSubmonoid R}

theorem mul_subset_mul : (↑M : Set R) * (↑N : Set R) ⊆ (↑(M * N) : Set R) := AddSubmonoid.smul_subset_smul

