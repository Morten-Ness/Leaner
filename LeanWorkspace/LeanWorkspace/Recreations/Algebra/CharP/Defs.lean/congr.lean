import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem congr {q : ℕ} (h : p = q) : CharP R q := h ▸ ‹CharP R p›

