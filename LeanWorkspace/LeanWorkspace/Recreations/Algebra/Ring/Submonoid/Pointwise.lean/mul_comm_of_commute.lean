import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

variable {M N P Q : AddSubmonoid R}

variable {ι : Sort*}

theorem mul_comm_of_commute (h : ∀ m ∈ M, ∀ n ∈ N, Commute m n) : M * N = N * M := le_antisymm (AddSubmonoid.mul_le.mpr fun m hm n hn ↦ h m hm n hn ▸ AddSubmonoid.mul_mem_mul hn hm)
    (AddSubmonoid.mul_le.mpr fun n hn m hm ↦ h m hm n hn ▸ AddSubmonoid.mul_mem_mul hm hn)

