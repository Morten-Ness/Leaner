FAIL
import Mathlib

variable {R : Type*} [NonUnitalSemiring R]

theorem inv_add_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u⁻¹.val.val + u.val.val + u.val.val * u⁻¹.val.val = 0 := by
  rcases u with ⟨a, b, hab, hba⟩
  exact hba
