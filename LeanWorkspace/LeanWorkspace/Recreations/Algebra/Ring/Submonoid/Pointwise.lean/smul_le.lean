import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoid R] [AddMonoid A] [DistribSMul R A]

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

theorem smul_le : M • N ≤ P ↔ ∀ m ∈ M, ∀ n ∈ N, m • n ∈ P := ⟨fun H _m hm _n hn => H <| AddSubmonoid.smul_mem_smul hm hn, fun H =>
    iSup_le fun ⟨m, hm⟩ => map_le_iff_le_comap.2 fun n hn => H m hm n hn⟩

