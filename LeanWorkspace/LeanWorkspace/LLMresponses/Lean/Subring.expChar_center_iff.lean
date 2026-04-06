FAIL
import Mathlib

theorem expChar_center_iff {R : Type u} [Ring R] {p : ℕ} :
    ExpChar (Subring.center R) p ↔ ExpChar R p := by
  constructor <;> intro h
  · letI : ExpChar (Subring.center R) p := h
    infer_instance
  · letI : ExpChar R p := h
    infer_instance
