import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem Commute.ringInverse_ringInverse {a b : M₀} (h : Commute a b) :
    Commute a⁻¹ʳ b⁻¹ʳ := (Ring.mul_inverse_rev' h.symm).symm.trans <| (congr_arg _ h.symm.eq).trans <|
    Ring.mul_inverse_rev' h

