import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R]

theorem ExpChar.congr {p : ℕ} (q : ℕ) [hq : ExpChar R q] (h : q = p) : ExpChar R p := h ▸ hq

