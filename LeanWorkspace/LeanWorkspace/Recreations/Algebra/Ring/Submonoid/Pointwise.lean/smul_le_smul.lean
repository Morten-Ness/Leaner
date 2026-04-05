import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoid R] [AddMonoid A] [DistribSMul R A]

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

theorem smul_le_smul (h : M ≤ M') (hnp : N ≤ P) : M • N ≤ M' • P := AddSubmonoid.smul_le.2 fun _m hm _n hn => AddSubmonoid.smul_mem_smul (h hm) (hnp hn)

