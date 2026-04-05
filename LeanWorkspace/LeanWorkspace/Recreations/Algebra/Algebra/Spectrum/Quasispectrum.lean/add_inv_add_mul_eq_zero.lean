import Mathlib

variable {R : Type*} [NonUnitalSemiring R]

theorem add_inv_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0 := by
  simpa [-Units.inv_mul] using congr($(u.inv_mul).val)

