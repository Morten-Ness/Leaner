import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoid R] [AddMonoid A] [DistribSMul R A]

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

theorem smul_subset_smul : (↑M : Set R) • (↑N : Set A) ⊆ (↑(M • N) : Set A) := smul_subset_iff.2 fun _i hi _j hj ↦ AddSubmonoid.smul_mem_smul hi hj

