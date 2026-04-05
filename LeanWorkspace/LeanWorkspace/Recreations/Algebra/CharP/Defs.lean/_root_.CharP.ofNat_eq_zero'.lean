import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem _root_.CharP.ofNat_eq_zero' (p : ℕ) [CharP R p]
    (a : ℕ) [a.AtLeastTwo] (h : p ∣ a) :
    (ofNat(a) : R) = 0 := by
  rwa [← CharP.cast_eq_zero_iff R p] at h

