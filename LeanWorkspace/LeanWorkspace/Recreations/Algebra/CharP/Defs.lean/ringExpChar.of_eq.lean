import Mathlib

variable (R : Type*)

theorem ringChar.of_eq ringExpChar [Ring R] [IsDomain R] {q : ℕ} (h : ringExpChar R = q) : ExpChar R q := h ▸ ringExpChar.expChar R

