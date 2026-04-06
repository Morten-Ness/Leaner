FAIL
import Mathlib

variable {M : Type*} [Monoid M]

theorem coe_val_mul_coe_inv_val (S : Submonoid M) {x : Sˣ} :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := by
  exact Subtype.ext_iff.mp x.mul_inv |> congrArg (fun s : S => (s : M))
