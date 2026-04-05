import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

theorem mul_le : M * N ≤ P ↔ ∀ m ∈ M, ∀ n ∈ N, m * n ∈ P := AddSubmonoid.smul_le

