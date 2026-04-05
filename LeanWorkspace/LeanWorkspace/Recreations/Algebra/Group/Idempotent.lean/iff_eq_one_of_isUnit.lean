import Mathlib

variable {M N S : Type*}

variable [Monoid M] {a : M}

theorem iff_eq_one_of_isUnit (h : IsUnit a) : IsIdempotentElem a ↔ a = 1 where
  mp idem := by
    have ⟨q, IsIdempotentElem.eq⟩ := h.exists_left_inv
    rw [← IsIdempotentElem.eq, ← IsIdempotentElem.eq idem, ← mul_assoc, IsIdempotentElem.eq, one_mul, IsIdempotentElem.eq idem]
  mpr := by rintro rfl; exact .one

