import Mathlib

variable {M : Type*} [Monoid M]

theorem coe_val_mul_coe_inv_val (S : Submonoid M) {x : Sˣ} :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := DFunLike.congr_arg S.subtype x.mul_inv

