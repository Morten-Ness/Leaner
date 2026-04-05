import Mathlib

theorem IsField.isDomain {R : Type u} [Semiring R] (h : IsField R) : IsDomain R where
  mul_left_cancel_of_ne_zero ha _ _ hb := by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [← mul_assoc, h.mul_comm, hx] using congr_arg (x * ·) hb
  mul_right_cancel_of_ne_zero ha _ _ hb := by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [mul_assoc, hx] using congr_arg (· * x) hb
  exists_pair_ne := h.exists_pair_ne

