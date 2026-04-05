import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoid R] [AddMonoid A] [DistribSMul R A]

variable {M M' : AddSubmonoid R} {N P : AddSubmonoid A} {m : R} {n : A}

theorem addSubmonoid_smul_bot (S : AddSubmonoid R) : S • (⊥ : AddSubmonoid A) = ⊥ := eq_bot_iff.2 <| AddSubmonoid.smul_le.2 fun m _ n hn => by
    rw [AddSubmonoid.mem_bot] at hn ⊢; rw [hn, smul_zero]

