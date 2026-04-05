import Mathlib

variable {M₀ : Type*}

variable {G₀ : Type*} [MonoidWithZero G₀] [IsLeftCancelMulZero G₀]

theorem iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 where
  mp h := or_iff_not_imp_left.mpr fun hp ↦ mul_left_cancel₀ hp (h.trans (mul_one p).symm)
  mpr h := h.elim (fun hp => hp.symm ▸ IsIdempotentElem.zero) fun hp => hp.symm ▸ one

