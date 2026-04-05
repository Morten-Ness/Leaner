import Mathlib

variable {R : Type*}

variable [Semiring R]

variable [Nontrivial R]

theorem IsMonicOfDegree.ne_zero {p : R[X]} {n : ℕ} (h : IsMonicOfDegree p n) : p ≠ 0 := h.monic.ne_zero

