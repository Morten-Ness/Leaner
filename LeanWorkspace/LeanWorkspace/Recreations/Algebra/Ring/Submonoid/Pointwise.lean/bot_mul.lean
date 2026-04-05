import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

theorem bot_mul (S : AddSubmonoid R) : ⊥ * S = ⊥ := eq_bot_iff.2 <| AddSubmonoid.mul_le.2 fun m hm n _ => by rw [AddSubmonoid.mem_bot] at hm ⊢; rw [hm, zero_mul]

