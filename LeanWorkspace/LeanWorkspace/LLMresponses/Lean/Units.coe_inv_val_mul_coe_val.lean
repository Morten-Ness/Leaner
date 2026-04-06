FAIL
import Mathlib

variable {M : Type*} [Monoid M]

theorem coe_inv_val_mul_coe_val (S : Submonoid M) {x : Sˣ} :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := by
  change (((x⁻¹ : Sˣ) : S) : M) * (((x : Sˣ) : S) : M) = 1
  exact x.inv_mul
