import Mathlib

variable {M : Type*} [Monoid M]

theorem coe_inv_val_mul_coe_val (S : Submonoid M) {x : Sˣ} :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.inv_mul

