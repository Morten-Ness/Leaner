import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoid R] [AddMonoid A] [DistribSMul R A]

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

theorem smul_le_smul_right (h : N ≤ P) : M • N ≤ M • P := AddSubmonoid.smul_le_smul le_rfl h

