import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsPrimePow.not_unit {n : R} (h : IsPrimePow n) : ¬IsUnit n := let ⟨_p, _k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').not.mpr hp.not_unit

