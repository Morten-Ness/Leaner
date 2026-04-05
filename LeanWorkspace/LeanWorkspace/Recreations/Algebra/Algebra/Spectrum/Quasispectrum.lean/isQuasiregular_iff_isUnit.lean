import Mathlib

theorem isQuasiregular_iff_isUnit {R : Type*} [Ring R] {x : R} :
    IsQuasiregular x ↔ IsUnit (1 + x) := by
  refine ⟨IsQuasiregular.isUnit_one_add, fun hx ↦ ?_⟩
  rw [isQuasiregular_iff]
  use hx.unit⁻¹ - 1
  constructor
  case' h.left => have := congr($(hx.mul_val_inv) - 1)
  case' h.right => have := congr($(hx.val_inv_mul) - 1)
  all_goals
    rw [← sub_add_cancel (↑hx.unit⁻¹ : R) 1, sub_self] at this
    convert this using 1
    noncomm_ring

-- interestingly, this holds even in the semiring case.

