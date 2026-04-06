FAIL
import Mathlib

variable {R : Type*} [NonUnitalSemiring R]

theorem add_inv_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0 := by
  cases u with
  | mk a b hab hba =>
      simpa using b.property a
