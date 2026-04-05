import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

theorem mul_mem_mul {m n : R} (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N := AddSubmonoid.smul_mem_smul hm hn

