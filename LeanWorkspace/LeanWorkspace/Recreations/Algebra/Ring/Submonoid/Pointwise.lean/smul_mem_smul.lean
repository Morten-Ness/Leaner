import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoid R] [AddMonoid A] [DistribSMul R A]

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

theorem smul_mem_smul (hm : m ∈ M) (hn : n ∈ N) : m • n ∈ M • N := (le_iSup _ ⟨m, hm⟩ : _ ≤ M • N) ⟨n, hn, by rfl⟩

